1. Quantifier and hypothesis audit
Bottom line
No: Corollaries 1.4 and 1.5 are not both true exactly as printed.
Corollary 1.4’s concrete 6-versus-7 clause is repaired correctly, but its general clause still suppresses a decisive map quantifier. Corollary 1.5 now puts the odd obstruction first, which is right, but its information bound still omits the protocol hypotheses, and the final assertion that the Fold6 “register bound is 0” does not follow from—and is not even well-defined in—the cited theorem’s model.
I also find two recurring scope losses elsewhere in the introduction:


the boundary-orientation claims omit the no-auxiliary-register/register-free hypothesis and replace uniqueness up to natural isomorphism with unqualified uniqueness;


the introductory register-capacity prose repeats Corollary 1.5’s omission of the deterministic universal-decoder model.


The abstract itself is now hypothesis-faithful.
Corollary 1.4
The first sentence begins:

“The concrete audited folds admit no fold-aware stable system over the boundary indicator that is fiberwise trivial over it, on any index set containing 6 and 7…”

That is exactly Theorem 3.7. The theorem quantifies over a fold-aware stable system on an index set containing 6 and 7, fixes the boundary statistics, and assumes fiberwise triviality over those statistics. The 3-versus-2 boundary-fiber mismatch then gives the contradiction.  
So the restored phrase “fiberwise trivial” fixes the concrete clause.
The next clause is not theorem-faithful:

“every fiberwise-trivial stable descent over a statistic is obstructed by comparable equal-statistic fibers of unequal cardinality.”

Theorem 3.6 says something more carefully quantified:


in an actual stable system, the two fibers paired by the actual structure map ρn,m​ must have equal cardinality;


to infer nonexistence before having such a system, one must show that every statistic-compatible candidate surjection
ρ:Xn​↠Xm​,sn​=sm​ρ,
produces at least one unequal-cardinality pair. 


The printed word “comparable” is undefined and hides this distinction. Mere existence of two fibers having the same statistic and different cardinalities is not enough: a candidate ρ might avoid pairing them. The obstruction concerns fibers paired by the actual map, or a mismatch for every admissible candidate map.
A faithful replacement is:

In every fold-aware system that is fiberwise trivial over compatible statistics, fibers paired by each structure map ρn,m​ have equal cardinality. Consequently, no such system exists between two levels if every statistic-compatible candidate surjection pairs at least one state with a fiber of unequal cardinality.

Verdict on Corollary 1.4: first clause true; second clause underquantified and not acceptable exactly as printed.
Corollary 1.5
The first two clauses are now right:


if one fiber has odd cardinality, no fiberwise fixed-point-free involution exists;


if every fiber has even cardinality, the exact number is the product of the perfect-matching counts. 


Those match Theorem 7.4(1)–(2). 
The next phrase is still too broad:

“selecting all of them requires at least the corresponding logarithmic message capacity.”

Theorem 7.4 does not state a model-free information bound. Its hypotheses are:


a deterministic protocol;


a finite message space R;


a fixed decoder
δ:R⟶Invfree​(p);


every admissible involution must be selectable, so δ is surjective.


Only under that model does
∣R∣≥#Invfree​(p)
and hence the logarithmic bound follow.  
“Selecting all of them” gestures toward surjectivity, but it does not carry the deterministic fixed-decoder and finite-message hypotheses. Given the history of this manuscript, those hypotheses must be printed, not inferred sympathetically.
The final sentence is worse:

“Invfree​ is empty for it and the register bound is 0.”

The first half is true: the Fold6 profile contains four fibers of size 3, so the odd obstruction makes the admissible set empty. 
The second half does not follow. In the model of Theorem 7.4:


log2​#Invfree​(p)=log2​0 is not 0;


a decoder from a nonempty message set into the empty set does not exist;


taking R=∅ leaves log2​∣R∣ equally undefined.


The proper conclusion is infeasibility, not zero information cost. A separate convention could assign zero cost to a vacuous “selection problem,” but that would be a new convention outside Theorem 7.4 and would conflict with the theorem’s decoder formulation.
A correct version is:

If some fiber has odd cardinality, no fiberwise free involution exists. If every fiber has even cardinality, their number is the stated product; in the deterministic finite-message decoder model of Theorem 7.4, any decoder capable of selecting every such involution requires at least the logarithm of that number in message capacity. The Fold6 system has odd fibers, so its admissible set is empty and the selection problem is infeasible; no register lower bound is asserted for it.

Verdict on Corollary 1.5: odd obstruction and even-fiber count pass; information clause is missing hypotheses; “register bound is 0” is false relative to the cited theorem.

The other numbered statements in the introduction
Theorem 1.1: passes
The residual, stochastic, off-grid spectral, 48-state minimality, uniqueness, quotient-spectrum and Q4​-carrier clauses are all stated for the audited window-6 fold and match the respective source results. 
In particular, the hidden-refinement clause reproduces Theorem 4.23’s actual hypotheses: an equitable surjection H:Ω6​↠Y together with a factorization of Fold6 through H. 
I find no missing quantifier in Theorem 1.1.
Corollary 1.2: not fully hypothesis-transparent
Corollary 1.2 says:

“every permutation-natural nontrivial binary jump structure factors uniquely through the sign character.”

Its sources make two qualifications explicit:


no auxiliary register is introduced;


uniqueness is up to natural isomorphism of torsor-valued functors.   


The authors can argue that “binary jump structure” is a defined term for the bare functor and therefore already excludes auxiliary registers. That defense is formally possible, but it is exactly the sort of hidden import that has repeatedly caused the front-matter failures here. Moreover, “factors uniquely” is stronger on its face than “is unique up to natural isomorphism.”
It should read:

every register-free, permutation-natural nontrivial binary jump structure is naturally isomorphic to the orientation torsor induced by the sign character.

This is a repair of hypothesis visibility and equivalence convention, not a mathematical change.
Corollary 1.3: passes
It explicitly says “for each fixed resolution m,” gives the product decomposition and the H1​,H2​ formulas, and then expressly denies cross-resolution invariance without stable descent. That matches Theorem 7.2.  
Proposition 1.6: passes
Its separation of classical spectral inclusion, paper-specific exact Fold6 computation, direct residual nonintertwining and supplementary spectral rejection is faithful to the proof chain. It does not promote the spectral criterion to a converse and does not claim that the averaged pushforward’s off-grid spectrum by itself excludes hidden refinements. 

Additional unnumbered front-matter sites
Introductory boundary-orientation paragraph
The introduction says that, once permutation naturality is imposed,

“the only nontrivial two-valued structure is the orientation torsor…”

but again omits the no-auxiliary-register condition and the natural-isomorphism convention. 
The phrase should be narrowed to “the only nontrivial register-free torsor-valued structure, up to natural isomorphism.”
Introductory register sentence
The introduction says:

“free involutions on fibers are counted by perfect matchings, giving a finite register lower bound for parity choices.”

The counting statement is fine, including count zero on odd fibers. The register conclusion is not automatic: it requires the deterministic finite-message universal-decoder model of Theorem 7.4. 
That sentence should either print the model or stop after the perfect-matching count.
Contribution item (iii)
Item (iii) says that the paper classifies permutation-natural binary jump structures and identifies “the boundary windows” in which central sheet parity can occur. 
It needs two restrictions:


“register-free permutation-natural”;


“among the audited windows m=6,7,8.”


The central-charge theorem is expressly restricted to m∈{6,7,8}. 
Defining the boundary sector to be empty at all other resolutions can make the broader sentence vacuously defensible inside this artificial certificate family, but it does not justify advertising a classification of all boundary windows.
Abstract
The abstract now passes. It confines the repair theorem to Fold6, accurately states the 48-state uniqueness and spectral multiplicities, describes the torsor and homology material as consequences of the finite fibers rather than universal fold theory, and explicitly labels the last-bit conclusions conditional on an additional homogenized hypothesis. 
So the abstract is not one of the remaining offending sites.

2. What the 15–20 page paper should be
The headline theorem
The headline is Theorem 4.23, not the spectral-rigidity theorem and not the certificate interface.
A suitable new main theorem is:

Unique minimal equitable repair of Fold6.
The 21-cell Fold6 partition of Q6​ is not equitable. Its unique coarsest equitable refinement is the orbit partition of the affine involution σgeo​. It has 48 cells—32 singletons and 16 pairs—and therefore every equitable hidden realization through which Fold6 factors has at least 48 states. The quotient spectrum has multiplicities
(1,5,11,14,11,5,1),
and the discarded 16-dimensional sector carries the adjacency operator of Q4​.

That is the theorem a combinatorics referee can value. The visible nonlumpability witness is its opening clause; the sharp 1/6 residual can be a strong supporting proposition. The determinant–Sturm eigenvalues are not a second headline: they are a redundant certificate for a failure already proved by a one-line neighbor-count discrepancy.
The current title should therefore be replaced by something such as:

The Unique Minimal Equitable Refinement of a Folded Partition of the 6-Cube

“Spectral rigidity” foregrounds the standard input rather than the new result.
A workable 18-page architecture
1. Introduction — 2 pages
State the new main theorem on page 1. Explain in one paragraph:


the Fold6 partition has 21 visible cells;


it is not equitable;


exact repair forces 48 cells;


the repair is unique and has an affine-orbit description.


Give only the immediate relationship to equitable partitions, color refinement and hypercube quotients. Delete the four-mechanism narrative, boundary torsors, homology, register entropy and conditional statistics.
2. The Fold6 partition — 2.5 to 3 pages
Retain from current §3:


the definition of Q6​, its walk and equitable partitions;


the equivalence in Lemma 3.1;


only the m=6 specialization of Definition 3.2;


the affine involution σgeo​;


a compact presentation of the Fold6 fibers.


The complete 64-vertex-to-21-cell table can be in an online supplement. In the article, print enough of it to define the partition unambiguously and to check the crucial refinement classes.
Delete Definition 3.4 and Theorems 3.5–3.7, Remark 3.8 and Proposition 3.9. Stable descent has no role in the repair theorem.
3. Visible nonlumpability and sharp residual — 3 pages
Compress Theorems 4.2, 4.12 and 4.13 into one elementary lemma:

For a partition F, visible ε-intertwiners are obtained by choosing each quotient entry in the intersection of the intervals centered at the normalized target-cell neighbor counts. Hence the sharp entrywise radius is half the maximum normalized diameter.

Then specialize:


print the two-vertex witness from Proposition 4.17;


state Δ6​=2;


conclude that the sharp real radius is 1/6;


retain the row-stochastic equality 1/6 as a short corollary, provided the endpoint-sum verification is moved to the supplement;


mention the averaged pushforward’s residual 1/4 in a remark, not in the main theorem.


The full (298,117,26) diameter distribution is certificate data, not article-level mathematics. Put it in the supplement.
4. Unique minimal equitable refinement — 5 to 6 pages
This is current Theorem 4.23 and must remain essentially intact.
Print the 48-cell neighbor-signature refinement table. Unlike the 21×21 edge matrix or the Sturm transcript, this table is not mere audit bulk: it is the combinatorial object whose properties prove the theorem.
The proof should retain the three decisive moves:


equality of Fold-neighbor signatures gives the displayed 48-cell refinement;


those cells are exactly the orbits of σgeo​, hence the partition is equitable;


every equitable refinement of Fold6 must refine the neighbor-signature partition, hence the 48-cell partition is uniquely coarsest.


That argument is the paper.
5. Quotient spectrum and discarded Q4​ carrier — 2.5 to 3 pages
Compress Theorems 6.1, 6.2 and Corollary 6.5 into a single lemma.
Explain directly that the exchange-complement involution decomposes the function space into invariant and antisymmetric parts; the antisymmetric part is canonically indexed by the remaining four coordinates, and adjacency there is A4​. Then derive:


the 16-dimensional discarded carrier;


the quotient multiplicity polynomial
(1+q)4(1+q+q2);


the multiplicities (1,5,11,14,11,5,1).


Delete the heat-trace terminology, cyclotomic commentary, exterior-algebra model and fold-observable orthogonality. None is needed to prove or understand the repair theorem.
6. Final remarks and reproducibility — 1 page
Give one paragraph on how the finite refinement can be independently recomputed. Point to the supplement containing:


the complete Fold6 fiber table;


the edge and residual streams;


the 48-cell refinement verifier;


optional exact matrices.


Do not reproduce hashes, manifests, environment contracts and expected transcript lines in the article.
That totals approximately 17–18 pages.

Disposition of the existing sections
Current materialDisposition in the cut paper§2, “Relation to other fold constructions”Delete outright. It is defensive project-boundary prose, not mathematics.§3 through Lemma 3.3Retain only the hypercube/equitability setup and the m=6 Fold definition.Definition 3.4–Proposition 3.9Delete outright.Theorem 4.1At most a one-paragraph standard remark; unnecessary once the determinant–Sturm route is removed.Theorems 4.2 and 4.13Merge into one compact residual lemma.Theorem 4.3, Theorems 4.7–4.12Delete. They repeatedly repackage the same neighbor-count criterion as an “interface,” “dichotomy,” “structure theorem” and “complete package.”Propositions 4.5–4.6Full data to supplement; only the defining Fold table needed in the body.Theorems 4.14–4.15Compress to one corollary; endpoint tables to supplement.Theorems 4.16–4.17Keep the maximum diameter, sharp radius and explicit witness; move the complete distribution out.Theorem 4.18Delete. It is a restatement of data already printed and cited.Lemmas 4.19–4.20 and Corollary 4.21Delete from the article. The off-grid eigenvalues add a second verification of nonlumpability, not a second mathematical result.Theorem 4.22Reduce to one paragraph explaining why visible nonlumpability does not exclude hidden refinements.Theorem 4.23Retain as the central theorem and proof.§5Delete entire section.§6.1–6.2 and Corollary 6.5Compress into one spectral-carrier lemma used by the main theorem.Remaining §6Delete.§7Delete entire section.§8Rewrite as at most one page.Appendix ADelete.Appendix BDelete.Appendix CMove to online supplement; replace in the article by one reproducibility paragraph.
Is there a genuine second result deserving its own note?
No.
There are two respectable supporting observations, but neither is a separate paper:


Theorem 4.13’s exact residual formula is useful, but mathematically it is the one-dimensional Chebyshev-center calculation for a finite family of intervals. It belongs as the lemma that turns the Fold6 count table into a sharp 1/6 result.


Theorem 6.1’s identification Am​∣V−​≅Am−2​ is elegant, but its proof is a basis calculation in which the two exchange-complement coordinate contributions cancel. It belongs as the spectral explanation of the 16 discarded modes.


The rest is less independent:


§5 is the sign character and orientation torsor of a finite set;


§7 is standard symmetric-group homology plus Künneth and perfect-matching counts;


Appendix A is determinant/sign functoriality;


Appendix B is conditional on an unproved homogenization hypothesis and therefore is not presently a theorem about the Fold family at all. The manuscript itself repeatedly describes these pieces as consequences, consistency checks or fixed-resolution calculus rather than coequal classification theorems.   


Nothing valuable is being “lost” in the research-result sense. What is being removed is an extensive halo of standard consequences around one finite structural theorem.
3. Strongest plausible journal for the cut version
The Electronic Journal of Combinatorics, with a rough acceptance probability of 25%—say a plausible range of 15–35%.
That estimate assumes the genuine rebuild described above: about 17–18 pages, Theorem 4.23 as the headline, direct neighbor-count nonlumpability, the complete minimal-refinement proof in the body, and computational audit material in a supplement.
This is not merely a topic match. The journal explicitly asks for papers of “substantial content” under very high standards, and it has published compact work combining structural arguments and exact computation for equitable partitions of particular hypercubes—for example, a 24-page paper giving theoretical and computational classifications for equitable partitions of Q12​. 组合数学杂志+1
The negative comparison is important: that Q12​ paper addresses classes of equitable partitions and closes parameter cases, whereas the present headline concerns one specifically constructed partition of Q6​. Your unique-coarsest-refinement theorem is strong enough to make submission plausible, but it remains a fixed small-instance theorem. That is why I put it at roughly one chance in four rather than near even odds.
I would not send the cut version first to the European Journal of Combinatorics: absent a family theorem or a new general classification principle, a referee there is likely to price the result as too local. A safer target after an Electronic Journal of Combinatorics rejection would be Discrete Mathematics, but the strongest venue at which I think a positive decision is genuinely plausible is the Electronic Journal of Combinatorics.
The present 80-page version is still a rejection. The remaining front-matter defects are locally fixable, but the architectural defect requires the radical extraction above, not another round of qualification sentences.
