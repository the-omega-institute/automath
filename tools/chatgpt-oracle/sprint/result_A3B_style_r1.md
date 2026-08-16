PART ONE — THE HOUSE STYLE, LEARNED FROM ACTUAL RECENT PAPERS
Scope note. I read the complete 36-page main article. The separate 15-page supplement was not present in the attachment. I can therefore judge its size and its declared function—the introduction describes it as containing entropy, Blackwell, pressure, fiber, discrepancy, bounded-multiple, zeta and geometric consequences—but I cannot give line-level comments on the supplement’s prose or proofs. 
1. What recent ETDS papers actually look like
There is no rigid ETDS template, but the recent symbolic-dynamics papers I checked are consistent enough to reveal a register.
How they open, and where the main theorem appears
A typical ETDS paper does not begin with the full main theorem in the first paragraph. It usually begins with the recognized dynamical object, the surrounding problem and a little history. The formal theorem then appears inside the introduction, before preliminaries and normally within the first two to four printed pages.
Jade Raymond’s 34-page paper first develops the group-theoretic and symbolic-dynamical setting, gives a motivating locally finite group example, and then states two main theorem blocks before the overview and Section 2. Bland–McGoff–Pavlov’s 34-page paper reviews the classical Zd result and the amenable-group setting before formally stating its generalization in the introduction, even though the theorem retains its later number “Theorem 4.2.” García-Ramos–Pavlov–Reyes state Theorem 1.1 after only a few contextual paragraphs and then begin preliminaries. Pavlov’s seven-page note spends proportionally more time on the conjectural history, but still states its main theorem before definitions and proof. 剑桥大学出版社+6剑桥大学出版社+6剑桥大学出版社+6
For a 30–40-page paper, an introduction of roughly three to five pages, around 8–15% of the article, is ordinary. Its purpose is not merely to inventory results. It normally does four things:


identifies a problem the field already recognizes;


explains what obstruction or gap remained;


states the principal results formally;


explains, after each principal theorem, what the conclusion means and why the hypotheses are natural.


The current manuscript has about one and a half pages of introduction before Section 2. That is not intrinsically too short, but most of that space is occupied by a theorem-number catalogue. It therefore has less genuine introduction than its page count suggests.
How much explanatory prose there is, and where it sits
In recent ETDS papers, the expository prose is unevenly concentrated. A 35-page paper may have several pages explaining the main question, half a page before a difficult construction, and almost no prose before a routine lemma. That unevenness is part of the journal’s mathematical register.
The prose normally sits:


in the introduction, around the principal theorem statements;


at the beginning of a major section, explaining the role of that section;


occasionally in one paragraph before a long proof, identifying the key idea;


in a remark after a theorem when there is a genuine interpretation, comparison or unresolved issue.


It does not normally sit in a throat-clearing paragraph before every definition and result. Nor does every consequence receive its own theorem-like block. Roughly speaking, in a long symbolic-dynamics article perhaps one fifth to one quarter of the text is explanatory rather than formal mathematics, but it is not uniformly distributed.
How proofs are written
ETDS expects the new central argument to be present in the article. A proof cannot merely say that the conclusion follows by “standard arguments” if those arguments contain the actual novelty.
Short proofs discharging their work to cited results are nevertheless entirely normal when the statement really is a corollary or application. For example, García-Ramos–Pavlov–Reyes prove a corollary by invoking a previously established result and then carrying out only the short remaining deduction. 剑桥大学出版社
Routine verifications are usually:


omitted as immediate;


given in one or two sentences;


bundled into a preliminary lemma;


or placed in an appendix when they are long but conceptually subordinate.


A central technical proof may be long. The journal does not demand artificial brevity. What it does demand is that the proof reveal its mechanism. A four-page proof made of a conceptual reduction followed by one difficult estimate fits. A four-page proof written as a branch-coverage audit, repeatedly certifying that no case has been omitted, reads less like ETDS even when mathematically sound.
Appendices and supplements
In the recent sample, appendices are absent more often than present. Raymond’s 34-page paper, Bland–McGoff–Pavlov’s 34-page paper, García-Ramos–Pavlov–Reyes’s 15-page paper and Pavlov’s seven-page note have no appendix in their article structures. 剑桥大学出版社+3剑桥大学出版社+3剑桥大学出版社+3
Where an appendix occurs, it has a narrow function. Ben Ovadia’s 33-page paper has an approximately one-page appendix collecting special notation. Li–Liu–Tu–Yu’s 20-page paper explicitly moves one complicated proof to Appendix A “for readability”; that proof occupies several pages, but it is one coherent technical unit, not a second portfolio of applications. 剑桥大学出版社+2arXiv+2
My practical read of the custom is therefore:


no appendix is common;


3–10% for notation, background or a technical verification is ordinary;


around 20–25% can be justified when it contains one genuinely complicated proof;


a supplement equal to 42% of the main article, containing eight different categories of consequences, is conspicuous.


Your ratio is 36:15, or 2.4:1. The supplement is about 29% of the total package and 42% of the main-text length. More important than the ratio is the kind of material being moved. ETDS appendices normally protect the reader from technical obstruction. Your supplement appears to remove a large collection of mathematical consequences from the argumentative narrative. That looks less like an appendix and more like a second article attached to the first.
Prose register
The normal register is direct first-person plural:

We prove…
We first establish…
The following proposition reduces the problem to…
Combining Theorems X and Y gives…

Impersonal prose is used where natural, but sustained passive voice is not the norm. Results are referred to by number. Motivation is usually stated once in the introduction and, when needed, once more locally in a more technical form. It is not repeatedly re-certified.
The current manuscript’s use of “we” is completely appropriate. Its difficulty is not voice. It is emphasis and repetition.
Tells of a paper that does not fit
The recurring non-ETDS tells are:


a main theorem that can be found only after navigating many preliminary “results” of equal typographical weight;


an introduction that is a theorem inventory rather than a mathematical argument;


a sequence of definitions and propositions proving facts every specialist would accept immediately;


lengthy defensive passages explaining what is not being claimed;


a proof written as an audit trail rather than an argument;


a detached supplement containing material readers would expect either in the paper or not in the submission;


a data or code section more detailed than the mathematical conclusion;


several substantial narratives joined only by a common notation.


The present manuscript exhibits most of these to some degree.

2. Application to this manuscript, section by section
Title and abstract
The title has the right nouns for ETDS: overlap, inverse depth, cyclic ranks and β-languages. It signals a symbolic-dynamical classification rather than a computational note.
The difficulty is the word “exact.” The abstract gives an exact quadratic threshold classification, exact local structure at several special loci, an exact longest-path formula for the simple-Parry quotient and an exact unbounded-depth family. But for negative-conjugate quadratic systems at m≥4, Theorem 4.7 gives only
2≤ℓcau​(β,m)≤m,
and the manuscript explicitly calls equality an open interface. 
That is not a correctness problem. The abstract itself says “future-only inverse bounds” for the quadratic part. It is a reader-expectation problem: the title makes it easy to expect a closed exact depth classification across both advertised classes. The exact graph formula in Section 6 can defend the title in an algorithmic sense, but that distinction is not made sharply enough at the beginning.
The abstract is also overfull. In one paragraph it gives:


the Fibonacci threshold and decoder;


low-window counterexamples;


the complete branch locus;


the quadratic threshold;


chamber duality;


inverse bounds;


a fixed-point normal form;


finite-block onset;


Fischer covers;


Markov order;


the simple-Parry quotient;


a trichotomy;


and a cubic unboundedness theorem. 


This is accurate, but it gives every result the same stress. An ETDS abstract should tell me what the paper changes about my understanding of the subject. Here the answer is obscured by the full inventory.
What to do instead: reduce the abstract by roughly one third. Give three results only:


the exact quadratic threshold classification;


the exact arithmetic collision-graph formula and aperture-two trichotomy;


the cubic family showing unbounded future-only depth.


The Fibonacci model, chamber duality, Fischer cover and Markov order can be presented as consequences in the final sentence.
Section 1: Introduction
The first three paragraphs are good. They define the transition from noninjective local windows to an invertible overlapped code, explain the cyclic rank construction and clearly distinguish it from numerical β-normalization. 
Then the introduction changes mode. “The Fibonacci model,” “The quadratic classification,” and “Simple-Parry quotients” become a theorem-by-theorem catalogue. The quadratic threshold formula is displayed, which is useful, but almost every later theorem is then named and summarized in sequence. 
There are three problems.
First, there is no formal principal theorem. The formula for the quadratic threshold appears, but the full theorem—including finite-block injectivity, conjugacy and the extremal families—does not appear formally until Theorem 4.5 on page 18.  Recent ETDS papers often preserve the theorem’s later number while reproducing the full statement in the introduction. This paper should do that.
Second, the introduction says what every theorem proves but gives too little explanation of why these are one theorem package. The missing conceptual paragraph is something like:

The local rule is arithmetically defined, but injectivity is a fiber-product question. In the quadratic case the recurrence gives direct separation; in the simple-Parry case the same collision problem closes on a difference quotient. The quadratic classification and cubic unboundedness are therefore two arithmetic realizations of one symbolic mechanism.

That is the paper’s argument. It should be the introduction’s centre.
Third, the companion-paper discussion occupies too much strategic space. The manuscript twice stresses that no theorem from the companion is used and that the papers share only the definition and a caution.  One concise sentence near the end of the introduction is enough.
What to do instead: expand the introduction to about three and a half pages, not by adding more literature, but by replacing the inventory with three formal theorem statements and explanatory prose after each. The roadmap should then be one paragraph.
Sections 2 and 3: Fibonacci stabilization and threshold
The Fibonacci model is a good opening example. The explicit three-window decoder is concrete and gives the reader an intelligible prototype before the two quadratic chambers.
The section is nevertheless overformalized. The “Basic properties of Foldm​” statement lists well-definedness, identity on admissible words, surjectivity and the fact that the fibers of a function partition its domain, and then proves each item in full.  That is exactly the kind of routine material an ETDS article compresses to a sentence after the definition.
Section 3 then packages several direct consequences as separate theorem-like units:


the algorithmic decoder;


the sliding-block decoder;


full one-sided block complexity;


one-sided conjugacy;


two-sided conjugacy;


finite-type closure;


invariant-measure correspondence;


decoder complexity;


and three subsequent remarks.  


Most are correct and useful, but the presentation removes hierarchy. The explicit decoder and sharp threshold are the mathematics. Continuity of the inverse, equality of block counts and pushforward of invariant measures are consequences.
What to do instead:


retain the finite-window range lemma, but halve its proof;


retain Lemma 3.1, Theorem 3.2, Proposition 3.3 and Theorem 3.4;


follow Theorem 3.2 with one corollary containing the decoder, conjugacy, SFT and complexity consequences;


give that corollary a proof of at most one paragraph;


retain only one interpretive remark explaining why degree one is arithmetic rather than formal resolving-map theory;


remove the invariant-measure bijection unless it is used later.


That would shorten Sections 2–3 by roughly three pages without losing mathematics.
Section 4.1: quadratic setup and rank
This section reads more like ETDS. The two chambers are set out, the Parry data are established and the rank intervals are proved directly because their endpoints are subsequently used. The opening paragraph gives a genuine mathematical reason for choosing the greedy language.
But it repeats the numerical-normalization disclaimer already made in the abstract and introduction.  Keep the disclaimer once in the introduction and once, in its most precise form, immediately after Definition 4.1. Delete later repetitions.
Proposition 4.2 is substantial enough to remain. Its proof gives the reader the exact interval decomposition on which the later cyclic fold depends.
Sections 4.2–4.3: the arithmetic core and threshold theorem
This is the mathematical centre of the paper, but it is not presently the rhetorical centre.
Lemma 4.3 occupies several pages. The proof repeatedly announces its exhaustiveness: it gives remaining Euclidean divisions “explicitly,” a “complete boundary sign audit,” explains that “no other quotient case” occurs, clears inequalities “line by line,” covers “all signs explicitly,” and then adds a separately labelled “Closure of the distance estimate.”  
This is the clearest place where the prose reads like a verification transcript rather than a mathematical proof. The estimate may genuinely require all these cases. The problem is the architecture. The reader is not shown a compact conceptual skeleton before entering the audit.
A better presentation would be:


derive the exact error identity;


state a small chamberwise sublemma giving the required unit separation;


prove the negative chamber by the norm argument;


prove the positive chamber’s finite integer exclusion in an appendix;


return immediately to the sliding-congruence lemma and threshold theorem.


Lemma 4.4 has the same issue at m=3: complete lists and overlap elimination are legitimate, but the lists should be in a table or appendix. The main text should explain why m=3 is exceptional and how the overlap rules eliminate the nonzero triples.
Theorem 4.5 itself is strong, clean and appropriately ETDS-like. It should arrive much sooner in the reader’s experience, either through a full introduction statement or by moving some technical proof detail behind it into an appendix.
Section 4.4: identifiability and local structure
This section contains valuable symbolic-dynamical consequences, but it is overloaded.
The chamber-duality theorem is conceptually interesting. The critical two-fixed-point normal form and its Fischer cover are directly relevant to ETDS. The exact finite-block onset and exact Markov order are also natural consequences of the main classification.  
The difficulty is Theorem 4.7 and Remark 4.1. The manuscript pauses to describe a conjectural negative-chamber equality, the finite evidence for it, the kind of bounded-carry invariant a proof would require and a particular invalid proof strategy.  This is honest, but too much of it belongs in a research notebook. In an ETDS article, the relevant statement is:

In the negative chamber we obtain the sharp value at m=3 and the bounds 2≤ℓcau​≤m for m≥4. Whether the lower bound is always attained remains open.

Two sentences suffice. The detailed warning about sorting multiples and quotient coefficients should be removed unless the literature contains a published argument that you are correcting.
The four worked cases are also too symmetrical. They instantiate all four combinations of chamber and extremality with nearly parallel prose.  A human-authored ETDS exposition would probably choose:


one extremal example, emphasizing the fixed-point collision;


one nonextremal example, showing the two-window decoder;


one two-row table giving the positive-chamber duals.


Section 5: metallic specialization
This should not be a separate numbered section.
The section explicitly says that its results are direct specializations of Theorems 4.5 and 4.9 and that no separate proof is required.  That is exactly when ETDS accepts a short citation-based proof—but as a corollary or subsection immediately after the general theorem, not as a separate narrative unit.
Move the formulas and Corollary 5.1 to the end of Section 4. Delete the concluding paragraph that again explains how the general theorem subsumes the Fibonacci and metallic conclusions.
Section 6: the simple-Parry quotient and cubic family
The first two paragraphs of Section 6 are among the strongest expository passages in the paper. They clearly separate the classical pair-graph decision from the new arithmetic difference quotient and identify what the quotient adds: exact future-only anticipation, a finite state bound and the zero-predecessor property. 
Unfortunately, this comes on page 25. Much of it belongs in the introduction.
Theorem 6.1 should be one of the formally stated introduction theorems. Its proof is appropriately short and structural. It establishes the exact correspondence between bounded difference vectors, graph paths and output collisions. This is recognizably an ETDS theorem.
The aperture-two trichotomy is also well placed and concise.
Proposition 6.4 is different. The fact that the theory genuinely extends beyond Pisot bases matters, but the detailed quartic example—including irreducibility, root counting and the conjugate-modulus calculation—is auxiliary. State the example in the main text and move most of its verification to an appendix.
The cubic family is a substantial second culmination. At present, however, the reader encounters several pages of Bassino-data verification and carry calculations before seeing Theorem 6.8. The section should begin by stating Theorem 6.8 and giving a three-paragraph proof roadmap. Lemma 6.5’s direct verification of the Parry data can move to an appendix. Lemmas 6.6 and 6.7 are the real new mechanism and should remain in the article, but their branch-exhaustion language should be reduced. The ending “with every carry and coordinate exhausted” is a particularly conspicuous audit-style phrase. 
Section 7: Conclusion
The conclusion repeats the full inventory, the companion-paper boundary and the supplement boundary.  It should instead answer one question:

What do we now know about inverse coding for these arithmetic sliding maps that we did not know before?

A good conclusion would have three short paragraphs:


exact quadratic threshold classification;


arithmetic quotient as the general collision mechanism;


unbounded cubic depth and the remaining negative-quadratic question.


No companion-paper sales paragraph and no supplement inventory are needed.
Data and code availability
This section is not in ETDS register. It lists five internal paths, all parameter ranges tested, several batteries, periodic-count ranges, representative systems and the exact status of the missing DOI. 
A journal article needs something like:

Source code for the finite computations and regression tests is archived at [repository/DOI]. These computations are not used as proofs of the parameter-uniform statements.

Everything else belongs in the repository README. A public archival identifier should be supplied before publication, as the manuscript itself already recognizes.

3. The main-text-to-supplement proportion
No: the present proportion is not right for ETDS.
A 15-page supplement attached to a 36-page main paper is already unusually large. A supplement containing eight kinds of downstream consequences is more problematic than a 15-page supplement containing one indispensable technical proof.
My recommended disposition is:
Move from the main article to an integrated appendix:


the detailed positive-chamber integer audit in Lemma 4.3;


the complete m=3 triple enumeration in Lemma 4.4;


most of the non-Pisot quartic verification in Proposition 6.4;


the direct verification of Bassino’s Parry data in Lemma 6.5;


any exhaustive finite tables.


Keep in the main article:


the Fibonacci decoder and threshold;


the quadratic threshold theorem;


the conceptual part of the sliding-congruence proof;


the chamber duality;


the critical fiber and Fischer cover;


the exact difference-quotient theorem;


the aperture-two trichotomy;


the two carry/path lemmas genuinely needed for the cubic unboundedness theorem.


Bring from the supplement into the main article only if not already present:


one concise corollary giving the essential dynamical payoff—fiber structure, entropy/periodic-point count or zeta—immediately after the relevant Fischer-cover theorem.


The present main already contains entropy and zeta information for the critical normal form, so corresponding supplementary material should not duplicate it.
Remove from this submission or develop separately:


a broad Blackwell theory;


a pressure package;


discrepancy consequences;


general geometric consequences;


a collection of bounded-multiple results not used in the main proof.


Those subjects may be good mathematics. As a set, they make the supplement look like a warehouse for everything implied by the construction.
A credible final shape would be approximately:


30–34 pages of main text;


6–8 pages of integrated technical appendices;


no separate supplement, or at most a very short computational supplement.


The target is not a numerical house limit. It is to make the main article carry the complete conceptual argument and the appendix carry only technical obstruction.

4. Does it read machine-assisted?
Yes, in several conspicuous passages.
I would not infer from that that the mathematics or authorship is inauthentic. But a referee sensitive to machine-assisted prose will notice the surface.
The strongest tells are:
Flat result weighting. The abstract gives almost every theorem one clause. The quadratic classification, a routine complexity count, chamber duality, an exact Fischer cover and the cubic unboundedness theorem all receive comparable emphasis. 
Exhaustive formalization of routine facts. The proof that a function’s fibers form a disjoint partition is carried out at the same formal level as a reconstruction theorem. 
Symmetrical packaging. Four worked cases cover the two chambers crossed with extremal/nonextremal status in almost mechanically parallel form. Two would be enough.
Repeated boundary policing. The statement that this is not numerical β-normalization occurs in the abstract, introduction, Section 4, Section 6 and conclusion.      One precise warning is valuable. Five resemble compliance checking.
Audit vocabulary. “Complete boundary sign audit,” “no other quotient case,” “clear the endpoint inequalities line by line,” “all signs explicitly,” and “every carry and coordinate exhausted” are not normal mathematical emphasis. They sound like a response to a verification checklist.
The data battery. The page-long inventory of every finite test range reads like generated assurance documentation rather than article prose.
Uniform transitions. Many transitions announce the administrative role of the next block—“the following…,” “we now…,” “the classification leaves three finer questions…”—without supplying a new mathematical reason. A human exposition ordinarily skips many of those transitions and spends its prose budget where the reader actually risks losing the idea.
The manuscript does not read machine-assisted everywhere. The explicit Fibonacci decoder, the interval proof of the rank bijection, the critical fixed-point analysis and the difference-quotient theorem have a definite mathematical voice. The machine-like surface is strongest in the framing, exhaustive case certification and consequences packaging. A serious compression pass would remove most of it.
PART TWO — YOU ARE THE REFEREE
Recommendation: MAJOR REVISIONS.
Dear Editor,
The manuscript studies cyclic recodings obtained by evaluating the positional rank of a legal word on the full digit alphabet, reducing modulo the number of legal words and overlapping the resulting finite-window maps. It gives an exact classification of the least injective aperture for quadratic Pisot systems, analyzes the local symbolic structure at and above threshold, constructs an arithmetic difference quotient of the classical pair graph for simple-Parry systems and applies it to obtain unbounded future-only inverse depth in a cubic Pisot family.
The results are substantial and the subject is appropriate for Ergodic Theory and Dynamical Systems. My recommendation is not driven by a mathematical objection to the principal results. It is driven by the fact that the current article has not yet been organized and written as one ETDS paper.
The principal difficulty is the absence of a sufficiently clear hierarchy. The title and abstract suggest a unified exact theory of overlap thresholds and future-only inverse depth. The body contains at least four substantial strands: the Fibonacci prototype, the quadratic threshold classification, the quadratic local-structure package and the general simple-Parry collision quotient with its cubic application. These strands are related, but the introduction presents them as an inventory rather than explaining the common mechanism. The reader is therefore asked to decide which theorem is the paper’s main theorem.
This problem becomes acute around Theorem 4.7. The quadratic threshold classification is exact, and the simple-Parry quotient gives an exact graph-theoretic formula, but the negative-conjugate quadratic future-only depth at apertures m≥4 is left between the bounds 2 and m. The authors are admirably explicit about this. Nevertheless, because exact inverse depth is part of the title-level promise, a reader can reasonably experience the result as incomplete rather than as a deliberately bounded component of a broader exact theory. The manuscript should either narrow the title and opening claims or supply the missing parameter-uniform quadratic equality. I do not regard new mathematics as necessary for publication if the claims are reframed precisely.
The introduction requires substantial rewriting. It should state the quadratic classification, the arithmetic pair-graph quotient and the cubic unboundedness result formally. At present the quadratic formula appears in the introduction, but the full principal theorem is postponed until page 18. The theorem-number catalogue should be replaced by an explanation of how the quadratic recurrence argument and the simple-Parry graph quotient solve the same collision problem in two regimes. The discussion of the companion manuscript should be reduced to one sentence.
Sections 2 and 3 contain too many separately packaged consequences. Well-definedness and surjectivity of the stabilization map, the partition into fibers, the algorithmic form of the decoder, block complexity, one-sided conjugacy, two-sided conjugacy, finite-type closure and invariant-measure transport do not each require separate formal treatment. The Fibonacci decoder, sharp threshold and branch locus should remain; most of the other material should be merged into one corollary.
The long arithmetic proofs also need editorial reconstruction. Lemma 4.3 is evidently important, but its present proof is written as a complete verification transcript. The conceptual reduction is difficult to see beneath Euclidean divisions, sign tables and repeated assurances that all cases have been covered. The main article should contain the reduction, the chamber split and the essential estimates. The longest bounded-integer audit may be placed in an integrated appendix. The same applies to the m=3 finite classification in Lemma 4.4.
Section 5 should be absorbed into Section 4. It is expressly a specialization of the general quadratic theorem, and a separate section gives it disproportionate weight. The four worked examples should be reduced to two examples and a small table.
Section 6 contains one of the paper’s strongest conceptual results, namely the exact difference quotient of the pair graph. This theorem should be advertised much earlier. Conversely, the direct verification of the quartic non-Pisot example and much of the Bassino input data can be relegated to an appendix. The cubic unboundedness theorem should be stated at the beginning of its subsection, before the technical lemmas proving it.
I am also concerned about the division between the 36-page article and the 15-page supplement. I have not seen the supplement itself, but the main article describes it as containing entropy, Blackwell, pressure, fiber, discrepancy, bounded-multiple, zeta and geometric consequences. That is not an ordinary technical supplement. It sounds like a second collection of results. The authors should retain in the article only those dynamical consequences needed to show the meaning of the classification, move genuinely technical verifications to an appendix and remove or separately develop the remaining downstream packages. In its present 36+15-page form, the paper appears broader but less coherent.
Finally, the prose needs a substantial reduction of defensive and audit-like language. The distinction from numerical β-normalization is important, but it need not be repeated in five locations. Similar comments apply to the repeated delimitation from the companion paper and to the standalone “What is and is not claimed” remark. The long data-and-code battery should be replaced by a conventional archival statement and moved to the repository documentation.
The single objection most likely to sink the paper is this: the manuscript does not establish a visible hierarchy matching its title. A referee can read it as an exact quadratic threshold paper, a partially explicit quadratic inverse-depth paper, a pair-graph quotient paper and a cubic family paper bound together by a common definition. The extensive supplement reinforces that impression. This objection is fixable. It requires a major architectural revision and either a narrower title or additional mathematics, but it does not require abandoning the central results.
I would not recommend acceptance in the present form, and the revision required is too extensive for a minor-revision decision. I would, however, invite a major revision rather than reject the paper, because the core theorems appear capable of supporting a focused ETDS article.
PART THREE — THE EDITOR’S BAR
Editorial decision: not acceptable in the present form; invite a major revision.
The following changes are ordered by importance.


Resolve the title-level promise of exact future-only depth.
Required — either craft or new mathematics.
This change must be made in the title, abstract, Introduction, Theorem 4.7/Remark 4.1 and Conclusion.
There are two acceptable routes.
Route A, requiring no new mathematics: remove the global implication that every quadratic future-only depth receives a closed exact classification. A suitable title would be:

Cyclic rank recodings of quadratic and simple-Parry β-languages: overlap thresholds and future-only inverse depth.

The abstract should then distinguish:


exact quadratic overlap thresholds;


exact depths in the positive chamber and at negative aperture three;


bounds in the remaining negative chamber;


the exact longest-path formula for simple-Parry systems;


exact depth in the cubic family.


Route B, requiring new mathematics: retain the present exactness framing and prove the negative-chamber equality for m≥4, resolving the interface now described in Remark 4.1.
I would not require Route B. Route A is sufficient for acceptance.


Rewrite the Introduction around three formal principal theorems.
Required — craft.
The revised introduction should be approximately three to four pages and should contain, in full or in a clean abbreviated form:


the exact quadratic-Pisot threshold theorem;


the arithmetic difference-quotient/longest-path theorem;


the cubic unboundedness theorem.


Each theorem should be followed by a paragraph explaining its dynamical meaning. The current paragraphs headed “The Fibonacci model,” “The quadratic classification” and “Simple-Parry quotients” should not remain as a theorem-number inventory.
Add one conceptual paragraph explaining that both main parts solve a common collision problem: direct recurrence separation in the quadratic case and a finite difference quotient in the simple-Parry case.
Reduce the companion-manuscript discussion to one sentence at the end of the introduction.


Rebuild the article around a single visible spine.
Required — craft and organization.
The preferred order is:


Introduction and main results;


common definitions and the compressed Fibonacci prototype;


quadratic rank data and exact threshold classification;


quadratic local structure and metallic corollary;


arithmetic pair-graph quotient for simple-Parry systems;


aperture-two trichotomy and cubic unboundedness;


conclusion;


technical appendices.


Section 5 should disappear as an independent section. Its formulas and Corollary 5.1 should become a subsection or corollary at the end of the quadratic section.


Replace the present 15-page supplement with a narrowly technical appendix.
Required — craft and selection.
On the information presently available, the revised submission should not retain a separate 15-page consequences supplement.
Move into an integrated appendix:


the longest bounded-integer/sign analysis from Lemma 4.3;


the complete m=3 triple lists from Lemma 4.4;


the detailed proof that the quartic example in Proposition 6.4 is non-Pisot;


the direct verification of Bassino’s expansion and recurrence data in Lemma 6.5;


computational tables or finite regression outputs, if any must be printed.


Retain in the main article only one short coherent dynamical-consequences subsection. It may include fiber structure, entropy, periodic points, zeta and Fischer-cover information directly tied to Theorems 4.8–4.9. Do not duplicate conclusions already stated there.
Blackwell, pressure, discrepancy, broad bounded-multiple and geometric packages should be removed from this submission unless the authors can show that one of them is indispensable to the main theorem’s interpretation. The natural alternative is a separate paper.
An appropriate target is six to eight pages of appendices, not fifteen pages of heterogeneous consequences.


Compress Sections 2–3 by removing theorem-level treatment of routine consequences.
Required — craft.
In Section 2:


combine Definitions 2.1–2.3 where possible;


retain the finite Zeckendorf range statement;


reduce the “Basic properties of Foldm​” proof to one sentence or delete the formal result.


In Section 3:


retain Lemma 3.1, Theorem 3.2, Proposition 3.3 and Theorem 3.4;


combine the algorithmic decoder, sliding inverse, block complexity, one- and two-sided conjugacy and SFT conclusion into one corollary;


remove the invariant-measure transport statement unless subsequently used;


combine Remarks 3.1–3.3 into one remark explaining the relation to resolving maps.


This should save at least two to three pages.


Rewrite the proof of Lemma 4.3 as an argument rather than an audit.
Required — proof presentation, not new mathematics.
The main-text proof should expose four steps:


the recurrence-ratio bounds;


the nearest-multiple reduction;


the positive- and negative-chamber separation mechanisms;


the conclusion for the distance estimate.


State the positive-chamber integer exclusion as a subsidiary lemma and place its exhaustive Euclidean case analysis in Appendix A. Keep the norm argument for the negative chamber in the main text, since it is conceptual.
Delete phrases whose role is only to certify completeness, including “complete boundary sign audit,” “no other quotient case,” “line by line” and similar language. Completeness should be apparent from the mathematical partition of cases.


Reorder and reduce Section 4 after the threshold theorem.
Required — craft.
Theorem 4.5 should be followed immediately by a paragraph explaining the extremal loci and why aperture two fails there.
Then arrange the consequences in this order:


chamber duality;


future-only depth statement, with the unresolved negative case stated in two sentences;


critical two-fixed-point normal form;


exact finite-block onset, Fischer cover and Markov order;


metallic corollary.


Reduce the four worked examples to two. A small table may record the two dual positive-chamber examples.
Delete Remark 4.2 as a standalone “What is and is not claimed” block. Retain at most one sentence after Definition 4.1 specifying that the map is not numerical normalization.


Make Theorem 6.1 and Theorem 6.8 visible before their technical machinery.
Required — craft.
Open the revised simple-Parry section with no more than two paragraphs of history and novelty.
State Theorem 6.1 prominently and retain its structural proof.
Keep Corollary 6.2 and the aperture-two trichotomy in the main article.
Convert Proposition 6.4 into a concise example, with its algebraic verification in an appendix.
Begin the cubic subsection with the statement of Theorem 6.8 and a proof roadmap. Then prove the two genuinely new ingredients—carry exclusion and terminal-path classification. Move the Bassino-data verification to the appendix.
Remove the duplicated transition on the present page 29, where unbounded depth is announced in two consecutive paragraphs.


Remove repeated defensive qualifications.
Required — craft.
The distinction from numerical β-normalization should occur:


once in the introduction;


once immediately after the formal definition of the cyclic rank map.


Delete its repetitions in the abstract, Section 6 and Conclusion unless a locally different issue is being addressed.
Similarly:


mention the companion manuscript only once;


do not twice certify that no companion theorem is used;


replace “genuine residual interface” with an ordinary open-problem sentence;


reserve adjectives such as “complete,” “sharp,” “exact” and “canonical” for places where they distinguish the result from a plausible weaker statement.




Rewrite the Conclusion and data statement.
Required — craft and publication mechanics.
The Conclusion should be no longer than one page and should contain:


the quadratic threshold classification;


the difference-quotient mechanism;


the cubic unboundedness result;


the one principal open question.


Delete the supplement inventory and the extended companion-paper comparison.
Replace the present data-and-code section with three to five lines giving:


the archival repository;


the DOI;


a statement that computations are regression tests rather than proofs.


The test matrix and internal paths must move to repository documentation. A persistent public archive should exist before final acceptance.


Carry out a deliberate de-flattening line edit.
Required — craft.
This is not ordinary copyediting. The revision should deliberately restore a human hierarchy:


allow the principal theorem several paragraphs of explanation;


allow routine consequences one sentence;


vary paragraph length according to difficulty;


remove transitions that merely announce structure;


combine parallel examples and statements;


stop formalizing facts that are immediate from definitions;


retain first-person plural, which already fits the journal.


The revised paper should no longer read as though every claim has been assigned the same template and verification burden.


Split the paper only if the unified rewrite does not work.
Discretionary fallback.
A split would produce:


one article on the quadratic threshold classification, branch locus, Fischer cover and Markov order;


one article on the simple-Parry difference quotient and cubic unbounded inverse depth.


I do not presently require this. The common collision mechanism is strong enough to support one article, provided the introduction and section order make that mechanism visible. A split becomes preferable only if the authors insist on retaining the full consequences supplement.


Mathematics versus craft
Only one possible acceptance item requires mathematics not currently in the manuscript:


the parameter-uniform exact value of the negative-conjugate quadratic future-only depth for m≥4, and only if the present global exactness claim is retained.


Everything else above is writing, selection, proof engineering and organization. Moving the positive-chamber integer audit to an appendix may require rewriting its proof, but not proving a new theorem. The same is true of the Bassino-data verification.
A revision satisfying Items 1–11 through the no-new-mathematics route would cross my editorial bar. I would not require the unresolved negative-chamber equality once the title, abstract and introduction accurately distinguish exact threshold classification, exact graph formulae, exact special-family depths and the remaining bounds.
