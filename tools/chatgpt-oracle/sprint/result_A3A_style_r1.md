PART ONE — THE HOUSE STYLE, LEARNED FROM ACTUAL RECENT PAPERS
Preliminary note on the submitted files
The uploaded PDF contains 20 pages total and ends with the data-and-code statement and bibliography. I do not see the advertised four-page technical audit supplement in the file available to me. I can therefore assess the proposed 20-page article plus four-page supplement architecture, but I cannot assess the supplement’s actual prose, necessity, or contents. 
1. What recent ETDS papers actually look like
There is no rigid ETDS template. Recent accepted papers range from short theorem papers to long conceptual constructions. Nevertheless, a recognizable norm emerges from papers such as Akiyama–Hichri’s Periodic expansion of one by Salem numbers, Mercat’s Geometrical representation of subshifts for primitive substitutions, Moss–Perrone’s categorical treatment of ergodic decomposition, Damanik–Lenz on uniform cocycles, Gorodetski–Kleptsyn on Lyapunov-exponent regularity, and Wormell on conditional mixing. These were published in ETDS between 2023 and 2025. ResearchGate+5剑桥大学出版社+5剑桥大学出版社+5
How an accepted paper normally opens
The prevailing ETDS pattern is:


Identify the mathematical object or phenomenon immediately.


Give enough background to make the question recognizable to the dynamical-systems reader.


State the first substantive theorem very early—often on page 2 or 3.


Explain what is new about the theorem and how it differs from the nearest existing mechanism.


Only then give the paper plan.


Akiyama–Hichri reach their principal theorem on the second page after a compact historical and arithmetic setup. Mercat states central results on the second page after identifying the substitution-dynamical problem. Gorodetski–Kleptsyn reach the main theorem around page 3 in an eleven-page paper. Damanik–Lenz begin stating their results on page 2, although their introduction and consequences continue for several more pages. arXiv+4arXiv+4arXiv+4
The major exception is a paper in which the preliminary framework is itself a large part of the contribution. Moss–Perrone delay their main theorem until a late section because the categorical architecture constructed before it is conceptually indispensable, not merely technical preparation. arXiv
For a paper of roughly twenty pages, the working norm is an introduction of approximately two to three pages, sometimes four when several communities must be connected. As a percentage, something around 10–17% is unremarkable. Length alone is not decisive. The question is whether each introductory paragraph performs a distinct job.
Explanatory prose versus theorem-and-proof prose
ETDS papers do not normally narrate every move. The characteristic distribution is uneven:


The introduction contains most of the broad motivation.


The opening of each technical section usually contains one orienting paragraph.


A long or conceptually non-obvious proof may receive a short roadmap immediately before it.


Inside the proof, prose is functional: it explains the key reduction, division into cases, or reason a construction works.


Consequences and limitations are usually placed in remarks after the theorem, but only when they sharpen the reader’s understanding.


In the body of a twenty-page theorem paper, formal definitions, statements, and proofs commonly occupy most of the space—perhaps two-thirds or more. There is no expectation that every lemma be preceded by a mini-essay. Conversely, an uninterrupted wall of formalism is also uncommon when a construction is not standard to the ETDS readership.
The normal unit is not “one explanatory paragraph per result.” It is “explanation where the conceptual burden changes.”
How proofs are written
A short proof that invokes cited results is entirely acceptable when the cited theorem genuinely does the mathematical work and the reduction is transparent. ETDS does not demand that authors reproduce standard symbolic-dynamical, ergodic, spectral, or automata arguments merely to make the proof longer.
But the paper must carry its own novel mechanism. Recent ETDS papers routinely:


cite a standard theorem in one sentence;


call a finite or routine verification direct;


omit algebra whose only purpose would be to reproduce a mechanical expansion;


move substantial background lemmas, computational algorithms, or technically distracting estimates into an appendix.


The distinction is between “routine but checkable” and “essential but omitted.” A proof may say that a finite list is checked directly if the list is genuinely small and the logical dependence is clear. It should not send the reader to a separate audit dossier to learn why the theorem is true.
Damanik–Lenz, for example, give short deductions when previous results immediately imply the claim, but carry the new cocycle arguments in the paper. Their appendices isolate relationships between existing notions and an auxiliary consequence of the Avalanche Principle. arXiv+1
Main text versus appendices or supplementary material
In short and medium-length ETDS articles, no appendix at all is common. Akiyama–Hichri, Mercat, and Gorodetski–Kleptsyn are examples from this sample. arXiv+2arXiv+2
When appendices are present, something around 5–20% of the complete article is ordinary. What is relegated is usually one of the following:


a standard but lengthy auxiliary result;


a technical estimate that interrupts the main argument;


an algorithm or computational protocol;


supplementary background needed by only part of the readership;


a proof of a secondary proposition used once.


Moss–Perrone have a roughly three-page appendix attached to a paper of about thirty pages. Damanik–Lenz devote approximately the last four to five pages of a twenty-four-page preprint to two integrated appendices. arXiv+1
Wormell is an important outlier: its appendices are very large because they contain genuinely substantial algorithms, error control, and proofs underlying the numerical part of the paper. They are integrated into the article, explicitly announced, and repeatedly used—not presented as an external audit certificate. arXiv+1
Accordingly, 20 pages plus four pages is numerically normal: the supplementary portion would be 16.7% of the full package. The questionable element is not the proportion but the description “technical audit supplement.” That is not a normal mathematical genre in ETDS. Proof-essential material should be an appendix to the article. Machine checks, regression tests, saved outputs, and checksums should normally remain in the code archive.
Register and signposting
First-person plural is completely normal:


“We prove…”


“We first reduce…”


“The following lemma identifies…”


“To establish the converse, we…”


Impersonal constructions are also common, but ETDS prose is not uniformly passive.
Results are normally referred to by number and by mathematical function: “Theorem 2.3 gives the required uniform estimate,” not by repeatedly paraphrasing the full theorem. Motivation is generally given once in the introduction and briefly recalled only when a later section changes viewpoint.
The prose is often less ceremonially polished than the present manuscript. That is not a criticism of ETDS papers. It means that accepted papers tend to sound authorial: the authors decide what deserves emphasis, abbreviate some routine matters, and spend disproportionate space on the one genuinely difficult transition.
Tells of a paper that does not fit the register
The most common stylistic warning signs are:


an abstract that inventories every lemma, qualification, application, and sharpness statement;


a long opening that explains the logical boundaries of the result more than its mathematical significance;


repeated assurances that the result is “not” various neighboring theorems;


a paper-plan paragraph that reproduces the table of contents sentence by sentence;


formal machinery introduced before the reader knows what dynamical question it resolves;


companion-paper management occupying visible space in the argument;


proof prose written like a verification certificate;


software-quality vocabulary—“regression,” “audit,” “falsification check,” “artifact”—inside a pure mathematical article;


identical rhetorical treatment of central theorems, minor caveats, finite checks, and bibliographic distinctions.


The underlying problem is not verbosity. It is failure of hierarchy.

2. Application to this manuscript, section by section
Title and abstract
The title is accurate, but overloaded:

Linear overlap transients for bounded zero representations in Pisot numeration: sharp inverse depth for cyclic rank recodings.

It contains the general theorem, its arithmetic object, the application, and the sharpness claim. That is one conceptual layer too many for a twenty-page article. ETDS accepts long titles, but the strongest titles usually identify one object and one phenomenon.
A cleaner version would be:

Linear overlap transients in Pisot numeration

or, if the symbolic-dynamical application must remain visible,

Linear overlap transients and cyclic rank recodings in Pisot numeration

This is discretionary rather than necessary.
The abstract is mathematically informative, but it tries to preserve almost the complete audit trail. It gives the general theorem, the collapse mechanism, the absence of Condition F, the exact quotient, the inverse-depth implication, the fixed cubic recurrence, the exact formula, the penultimate obstruction set, emptiness of the next set, and two different sharpness consequences. 
That produces the first instance of flat emphasis: the reader receives no rhetorical signal that the primary result is the linear transient theorem, while the exact set {Em​,−Em​} is supporting sharpness data.
The abstract should be reduced by roughly one quarter. Keep:


the general linear transient theorem;


one sentence on the adjacent-collapse mechanism;


the exact collision-quotient application;


one sentence saying a fixed cubic system has exact asymptotically linear depth.


Remove from the abstract:


the explicit penultimate obstruction set;


the statement that “the next set is empty”;


one of the two formulations of sharpness;


the detailed Condition F sentence, unless that distinction is central to the novelty claim.


Introduction
The introduction begins well. The first paragraph identifies a standard finite-state object, distinguishes regularity from a quantitative transient problem, and formulates the question concretely. The next paragraph gives the linear answer. This is close to ETDS practice. 
The formal theorem does not appear until page 8, but this is not by itself a problem because the result is stated clearly in prose on page 2. Still, the introduction would read more like a recent ETDS article if it contained three concise displayed statements:


Theorem A: the linear transient bound;


Theorem B: the inverse-depth consequence;


Theorem C: the fixed cubic sharpness result.


At present, formulas labelled (A1) and (A2) do some of this work, but the first and most important theorem is only narrated. A three-result hierarchy would make the paper easier to evaluate and would prevent the cyclic-rank application from appearing to compete with its own input theorem.
The proof synopsis is useful but too detailed. The paragraph beginning with the contracting conjugates tells the reader the exact expression that vanishes, the successive values of the quotients, the exceptional appended coefficient, the arrival at the zero state, and the small-aperture algorithm.  One or two of those details should be saved for Section 2. In the introduction, it is enough to say that comparison of consecutive zero representations forces all later quotients to vanish once the aperture crosses an effective threshold, after which the overlap path reaches the zero loop in at most linear time.
The next paragraph is the first major register departure:

“The proof requires neither Condition F nor preservation of leading zeros… Conversely, our result does not assert finite expansion, normalization complexity, or a general synchronization theorem…”

This sounds like a response to a scope objection rather than the natural exposition of a theorem.  Keep one positive boundary sentence:

“The argument uses only the Pisot contraction and the recurrence weights; it does not require Condition F.”

Delete the subsequent list of things not proved. Those distinctions can be made once in the literature discussion if genuinely necessary.
The cyclic-rank passage is mostly successful. It explains the construction and makes clear that it is a congruence of language ranks rather than numerical β-normalization. The exact quotient and causal inverse statement are intelligible. 
But the sentence

“This is a consequence of the bounded-zero theorem and the exact quotient, not the definitional center of the argument”

is editorial self-commentary. It tells the reader how the authors want the work valued rather than advancing the argument. The hierarchy should be created by the ordering and theorem statements, not declared in this way.
The comparison with pair graphs, Ashley’s decoder bounds, and bounded-delay rational relations is useful and belongs here.  It would be stronger if preceded by one sentence stating the independent dynamical significance:

“Thus injectivity of this family of sliding codes controls not merely the existence of a finite inverse window but its growth with the aperture.”

That sentence is presently implicit.
The fixed cubic result is appropriately introduced and gives the paper a strong end point.  The last clause—explaining that the same object proves sharpness twice—is worth retaining.
The organization paragraph is longer than needed and gives the companion manuscript too much prominence.  Reduce it to two sentences. Mention the companion paper once, either here or in Section 5, not both.
Overall introduction judgment: its length is acceptable; its architecture is good; approximately one page of its prose should nevertheless be rewritten or removed because it is defensive and too exhaustive.
Section 2: overlap chains and the linear transient theorem
This is the most naturally written section of the paper.
The direct opening with the recurrence and its Binet expansion is appropriate. The effective growth constants are introduced because they are immediately needed. 
The graph definition is clear, as is the explanation of why first-coordinate-nonzero vertices are distinguished.  Before the separation constant δU,D​, add a two-sentence roadmap:

“The proof compares two adjacent edges through all embeddings of the Pisot field. The following constants bound the conjugate contributions and separate the finitely many possible dominant-embedding defects from zero.”

That would help an ETDS reader understand why the constants are appearing.
Lemma 2.1 and its proof are well judged. The proof is short because the right identity has been found, not because work is being hidden. It carries the novel argument in the article and does not discharge it to an audit or citation.  This is entirely acceptable ETDS proof style.
Theorem 2.2 unnecessarily repeats the full graph definition immediately after it was given.  Replace the repetition with:

“Let Gm​(U,D) be the graph defined above.”

The theorem would then be substantially easier to see on the page.
Its proof is excellent in proportion: one paragraph for large apertures, one for the finite exceptional set. The exact longest-path search is an acceptable treatment of the routine finite part because the large-aperture mechanism is proved analytically. 
The global chain dichotomy should be made a short corollary rather than left as an unlabelled continuation.  It is a genuine conceptual consequence and deserves more emphasis than the boundary inventory that follows it.
Remark 2.1 is the clearest stylistic misfit in the main article. It lists seven objects not used and then another list of five subjects not covered.  It reads like a formal response to earlier criticism:

no canonical rank bijection, legal-word alphabet, cyclic reduction map, positive/negative realization, image shift, inverse decoder; not numerical normalization, carry propagation, synchronized transductions, right-closing maps, or broad sliding-block codes.

A human-authored ETDS version would select the one distinction most likely to prevent misunderstanding. Reduce the remark to approximately three sentences:

“Theorem 2.2 is independent of the cyclic-rank construction of Section 3. Its essential arithmetic features are the distinguished terminal weight um​ and the use of consecutive recurrence weights; replacing um​ by an unrelated modulus removes the identity underlying Lemma 2.1. The theorem should therefore not be read as a general statement about arbitrary sliding block codes.”

That says everything a reader needs.
Section 3: cyclic rank recodings
The section is mathematically efficient but needs a little more conceptual orientation. Its opening moves rapidly through nonstandard initial values, the canonical digit set, legal words, rank, modular folding, the sliding code, and the causal inverse length. 
Add one short paragraph before the definitions:

“We now pass from the arithmetic overlap graph to a family of sliding codes. Equality of two folded output windows is a congruence of their raw ranks; taking coordinatewise differences will turn a collision of the code into exactly the bounded zero representations considered in Section 2.”

That is the conceptual spine of the section. It should precede the notation.
Lemma 3.1 is strong and appropriately concise. The positive/negative-parts argument establishes that the quotient loses no collisions, and the additional paragraph dealing with the zero loop closes a real logical point without over-explaining it.  This is good journal prose.
Corollary 3.2 is also properly proportioned: a short application of the theorem after the exact graph identification. 
The final paragraph again sounds like a rebuttal:

“The scope is not a disguised standard-initial-value convention…”

followed by examples concerning k-bonacci initial values and Condition F.  The mathematical information is useful, but the tone should be changed. State it positively:

“The corollary applies to nonstandard initial values as long as the sequence is strictly increasing. It also applies beyond Condition F; for example…”

One example is enough.
Section 4: the fixed cubic system
This is the most convincing part of the manuscript as an ETDS article. It is specific, uneven in the right way, and visibly governed by the mathematics rather than by a presentation template.
The theorem gives an exact inverse length, the exact terminal obstruction set, and a matching lower bound for the general graph theorem.  The last three caveat sentences in the theorem statement should be moved to a remark. A theorem statement should finish on the sharpness conclusion, not immediately qualify the numerical optimality of unrelated constants.
The proof carries the argument. It establishes the Pisot and Parry facts, derives the coefficient bounds, verifies the contraction threshold, obtains the suffix-sum identity, and then treats even and odd apertures differently.  The terminal analysis is concrete and appropriately receives several pages rather than being reduced to “a calculation.”  This is exactly the purposeful unevenness missing from some of the framing prose.
The finite m=4,5 table is acceptable in the main text. The explanation that the calculation is exhaustive because each quotient lies in {−1,0,1} and the last digit successively determines the preceding one gives the reader a mathematical reason to trust it. 
If the missing four-page supplement merely prints further instances, scripts, or machine output supporting these two cases, it should not accompany the paper as a mathematical supplement. If it contains a human-readable proof of an assertion used here, that proof should be integrated as Appendix A.
Section 5: comparative context
This section contains legitimate distinctions but is the least ETDS-like section.
The opening fixed-system versus varying-system comparison is useful.  Move it to the introduction immediately after the sharpness theorem.
The next paragraph explaining that the simple-Parry identification supplies the language but that the proof itself uses only the recurrence and terminal equations is also useful.  It belongs as a remark after Theorem 4.1.
The discussion of the quadratic classification and the companion paper is too detailed for this article.  It advertises results not proved here and risks making the submitted article look like one administratively extracted portion of a larger manuscript. Replace it with one sentence:

“Related exact classifications for quadratic and simple-Parry systems are developed in the companion paper [11], none of whose results is used here.”

The last paragraph explains for the third time what “sharpness” means.  The distinction between order sharpness and optimality of the computed constant should be made once, directly after Theorem 4.1. The rest can be deleted.
I would therefore eliminate Section 5 as a separate section. Redistribute about half a page of it and delete the remainder. This single change would make the article feel substantially more like a finished ETDS paper and less like a reconciled project dossier.
Data and code availability
The inclusion of a code statement is unobjectionable. The register is not.
Phrases such as:


“regression and falsification checks,”


“seven-edge regression,”


“audited range,”


“saved outputs, reproduction commands, and checksums”


belong naturally in a repository README, but they sound like software-quality assurance in the article. 
Use something like:

“Code verifying the finite computations in Section 4 is included in the accompanying source archive. In particular, it checks the cases m=4,5, the recursive terminal words, and the finite obstruction calculations. These computations are supplementary to the uniform analytic proofs.”

The exact filenames may be retained, but the checksums and testing vocabulary should remain in the archive.

3. The main-text-to-supplement proportion
The numerical proportion is right; the proposed genre may not be.
A 20-page main article plus four pages of appendix material is fully within ETDS custom. Four pages would be:


20% relative to the main article;


16.7% of the complete 24-page paper.


That is a normal appendix proportion.
What should happen depends on the missing supplement’s content:


Proof-essential estimates, finite classifications, or omitted arguments: move them into a labelled Appendix A in the article.


Additional examples illustrating the terminal recursion: an integrated appendix is reasonable but not necessary.


Code listings, machine output, hashes, regression tests, audit tables: leave them in the source repository; do not submit them as a four-page mathematical supplement.


A prose certificate explaining that scripts agree with the theorem: omit it.


The correct ETDS package is likely either:

20–22 pages of article including a short integrated appendix, plus a code archive,

or simply:

the present article, stylistically revised, plus the code archive.

4. Does it read as machine-assisted?
Parts of it do. The mathematical proofs generally do not.
The detectable feature is not bad grammar or mathematical vagueness. It is an over-controlled rhetorical surface.
The introduction proceeds through nearly equal units:


question;


theorem;


proof mechanism;


scope exclusions;


application;


literature exclusions;


sharpness;


organization and companion paper.


Every element receives a complete, polished paragraph. That is precisely the flatness of emphasis described in the question. A human ETDS introduction would probably spend more space on why the inverse-depth problem matters, less space on neighboring claims that are not being made, and almost no space explaining which companion article owns which classification.
There are also repeated symmetrical templates:


“The proof requires neither… Conversely, our result does not…”


“This is a consequence of… not the definitional center…”


“The fixed cubic theorem and the broader family results answer different questions. By contrast… Conversely…”


“No result from that article is used… the only shared material is…”


These sentences are grammatical and accurate, but collectively they sound generated or committee-reconciled.   
The strongest machine-assisted tell is Remark 2.1. A human mathematician ordinarily does not enumerate twelve adjacent subjects that a theorem is not about unless responding directly to a referee or priority dispute. 
The terms “logical boundary,” “definitional center,” “limited comparison,” “regression and falsification checks,” and “audited range” reinforce the impression that the article has inherited language from assessment documents.
By contrast, the proof of Theorem 4.1 does not have this flatness. The even case receives one treatment, the odd case another; one finite calculation is displayed, another is summarized; the proof slows down where the terminal patterns branch and moves quickly where the recurrence propagates uniquely.  That part sounds like a mathematician following the proof.
My blunt diagnosis is:

The paper does not read as machine-generated mathematics. It does read as mathematically sound prose that has been repeatedly machine-assisted, audited, and reconciled until too many boundaries are explicit.

The remedy is deletion and redistribution, not an attempt to make the language more colloquial.

PART TWO — YOU ARE THE REFEREE
Recommendation: ACCEPT WITH MINOR REVISIONS
To the Editor,
The manuscript proves an effective linear bound for transient paths in one-position overlap graphs of bounded representations of zero associated with a fixed Pisot recurrence. Its principal technical input is an adjacent-collapse lemma obtained by comparing two consecutive zero representations under the algebraic embeddings of the Pisot field. The contracting embeddings uniformly bound the nondominant terms, while an effective finite separation in the dominant embedding forces the later quotient to vanish. The resulting path reaches the zero loop after linearly many overlaps unless a directed cycle is already reachable.
The paper then identifies the coordinate-difference graph of a cyclic language-rank recoding with the same bounded-zero graph. This gives a linear future-only inverse-depth bound under injectivity. Finally, a fixed cubic simple-Parry system is treated exactly: the inverse length is 2⌊m/2⌋−1, the terminal obstruction set is classified, and the same words establish sharp linear order for the general transient theorem.
The mathematical architecture is coherent. The general graph theorem is proved before the symbolic-dynamical application; the collision quotient is exact rather than merely an upper comparison; and the sharpness example is carried analytically in the article rather than presented as experimental evidence. The principal proofs are concise but not skeletal. In particular, Lemma 2.1 contains the essential dominant-embedding identity and Theorem 2.2 makes the finite-exception argument effective.  The proof of the cubic theorem is long enough to make the terminal classification credible and self-contained. 
In my view, the paper is suitable in subject and scale for ETDS. It connects a finite-state arithmetic object in Pisot numeration to a quantitative inverse-coding question and proves an order-sharp bound in one fixed system. I would not require a further theorem or a broader family classification as a condition of publication.
I do, however, recommend revision of the exposition before acceptance.
The main issue is that the article explains its boundaries too insistently. Several passages read as responses to earlier objections rather than as part of the natural mathematical narrative. The introduction lists properties not assumed, results not implied, neighboring theories not covered, and the exact division of material between this article and a companion manuscript. Remark 2.1 gives an especially extensive negative inventory.   Section 5 repeats many of the same distinctions after the proof is complete. 
This material obscures rather than protects the central contribution. The paper should state positively what structure the proof uses, explain once why the result is not a consequence of existing finite-state recognition or generic pair-graph bounds, and then proceed. It does not need to enumerate every nearby assertion it avoids.
I also recommend that the three-result hierarchy be made more visible in the introduction. The general transient theorem is described early, but unlike the inverse-depth and sharpness results it is not given a compact displayed introductory statement. A Theorem A/Theorem B/Theorem C presentation would help an ETDS reader see immediately that the cyclic rank construction is an application of an independently formulated overlap theorem and that the cubic theorem establishes matching order.
Section 5 should not remain in its present form. Its useful material can be redistributed: the fixed-system versus varying-system distinction belongs in the introduction; the observation about which simple-Parry facts are used belongs after Theorem 4.1; and the companion article needs only one sentence. The remainder is repetitive.
The code-availability paragraph should also be rewritten in ordinary mathematical register. The exact filenames may be retained, but language about regression tests, falsification checks, audit ranges, and checksums is better placed in the repository documentation. 
I have not received the stated four-page technical supplement. If it contains any argument essential to the proofs or to the exact terminal classification, that material should be incorporated as an appendix to the paper. If it contains only program output, testing records, or reproducibility metadata, it need not form part of the submitted article.
The objection most likely to sink the paper
The most serious presentational risk is that the repeated boundary management and companion-paper discussion make the manuscript look like an extracted technical slice of a larger classification project, rather than a standalone ETDS article with its own conceptual arc.
That objection is fixable. The actual mathematical arc is already present:
bounded-zero overlap theorem⟶exact collision quotient⟶inverse-depth consequence⟶fixed-system sharpness.
The revision should allow that arc to carry the paper without repeatedly explaining what has been assigned elsewhere.
Subject to these presentational changes and appropriate treatment of the missing supplement, I recommend acceptance with minor revisions.

PART THREE — THE EDITOR’S BAR
Editorial decision
I would issue a minor-revision decision. I would accept the article once the required items below had been completed.
No additional theorem, generalization, or mathematical application is required on the evidence of the twenty-page article. The remaining gap is overwhelmingly one of writing, hierarchy, and packaging.
1. Required — Rewrite the abstract around one primary result
Type: craft.
In the abstract, make the linear transient theorem the unmistakable center. Retain the collapse mechanism, state the inverse-depth application in one sentence, and summarize the cubic example as exact order sharpness.
Delete the explicit description of the penultimate set {Em​,−Em​} and the next-set emptiness from the abstract. Those are proof-level details. 
2. Required — Give the introduction an explicit theorem hierarchy
Type: craft and organization.
After the first problem paragraph, state three compact introductory results:


the linear overlap-transient theorem;


the inverse-depth corollary;


the fixed cubic sharpness theorem.


They need not duplicate every effective constant or graph definition. Their purpose is to make the logical hierarchy visible by page 2 or 3.
Shorten the detailed synopsis of the adjacent-collapse proof. Preserve the idea—contracting conjugates plus finite dominant separation—but leave the successive quotient identities to Section 2. 
3. Required — Remove the audit and rebuttal register
Type: craft.
Rewrite or delete the following:


the negative inventory following the first theorem discussion; 


“not the definitional center of the argument”; 


most of Remark 2.1; 


“not a disguised standard-initial-value convention”; 


the repeated clarification of what sharpness does and does not mean. 


Each boundary should be stated at most once and positively whenever possible.
4. Required — Eliminate Section 5 as a separate section
Type: craft and organization.
Redistribute its useful material as follows:


Move the fixed-system versus varying-system comparison to the introduction.


Put the explanation of which simple-Parry facts are actually used in a remark after Theorem 4.1.


Reduce the companion-paper discussion to one sentence.


Place the order-sharpness qualification in one remark after Theorem 4.1.


Delete the remaining repetition.


The revised paper should move directly from the fixed cubic proof to the data/code statement or acknowledgments. 
5. Required — Resolve the four-page supplement
Type: packaging; conditionally mathematical.
Because it was not included in the uploaded PDF, this requirement is conditional on its contents.


If it contains proof-essential reasoning, incorporate it into a conventional Appendix A in the article.


If it contains only expanded finite verifications that are not logically essential, retain at most the human-readable part in a short appendix.


If it consists of scripts, outputs, test logs, hashes, or an audit certificate, do not submit it as mathematical supplementary text. Keep it in the source archive.


No theorem may depend on an argument that appears only as machine output or as a verification assertion.
This is the only item that might require additional mathematical writing. It should not require new mathematics unless the supplement currently conceals an unproved step.
6. Required — Reduce the companion-manuscript footprint
Type: craft and standalone positioning.
The companion article is presently mentioned in both the introduction and Section 5, with a detailed catalogue of what it contains.  
Mention it once:

“Related exact classifications for quadratic and simple-Parry systems are obtained in [11]; no result from that paper is used here.”

Do not enumerate its Fibonacci model, Fischer covers, Markov order, family unboundedness, and other contents. That catalogue makes the current article appear dependent on the larger project even while asserting the opposite.
7. Required — Add a conceptual bridge at the start of Section 3
Type: craft.
Before introducing the legal words and the fold map, add four or five sentences explaining:


what dynamical object is being coded;


what “future-only inverse” means conceptually;


why equality of folded windows becomes a modular rank collision;


why coordinate differences should produce zero representations;


why exactness of that quotient matters.


The current definitions are correct but arrive before the reader has been told the section’s mechanism. 
8. Required — Streamline the formal presentation in Section 2
Type: craft.
Do not repeat the complete definition of Gm​(U,D) in Theorem 2.2. Refer to the preceding definition. 
Turn the global chain dichotomy into a labelled corollary. 
Retain the full proof of Lemma 2.1 and the large-/small-aperture division in Theorem 2.2. Those are already at the correct level of detail.
9. Required — Rewrite the code-availability statement
Type: craft.
Replace software-audit vocabulary with a neutral description of the finite computations verified by the accompanying code. Move checksums, commands, regression terminology, and the detailed testing account into the repository documentation. 
10. Discretionary — Shorten the title
Type: craft.
The present title is acceptable but crowded. I would prefer:

Linear overlap transients and cyclic rank recodings in Pisot numeration

or simply:

Linear overlap transients in Pisot numeration

This is a matter of editorial taste, not a condition of acceptance.
11. Discretionary — Add one small motivating example
Type: exposition; no new mathematics.
A five- or six-line example near the beginning of Section 2 or Section 3 could display:


two overlapping zero representations;


the corresponding edge transition;


or two raw windows giving the same folded output.


This would help a symbolic-dynamics reader parse the construction before encountering the general notation. It is not necessary if the introductory conceptual bridge is strong.
Final editorial assessment
The article is already inside the normal ETDS range in length, proof density, theorem scale, and appendix proportion. It is not a major-revision paper, and it does not need another mathematical result to justify submission.
The remaining obstacle is that some of the prose still behaves like a record of the manuscript’s previous audits: it preserves every boundary, distinction, qualification, and allocation of material. Removing that layer would leave a concise and recognizably ETDS-style paper whose mathematical hierarchy is already sound.
