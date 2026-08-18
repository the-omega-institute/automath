(1) Is there a short paper inside the 48 pages?
Yes, but only one result besides the headline is independently publishable: Theorem 5.14.
The viable second paper is not really about rotation dynamics. It is the exact injective-placement problem:

Given the fixed m+1 atom weights of the Sturmian m-block law, how should those atoms be injected into the golden-mean m-block language to minimize Rényi divergence from the Parry law?

For m≥6, Theorem 5.14 gives the exact minimum simultaneously for every Rényi order, shows that placing the atoms in the 00-endpoint class is optimal, identifies all finite-q optimizers, and separately characterizes the extra q=∞ optimizers.  That is a real, closed finite optimization theorem, not merely a numerical consequence of Theorem 4.1.
Its engine is Theorem 5.12: because golden-mean Parry cylinder weights have only three levels, the maximal Parry mass of a k-point support is found by filling the endpoint classes in descending order.  Theorem 5.14 then keeps the source weights fixed rather than optimizing over all laws. The threshold m=6 comes from the exact capacity condition
∣Xm00​∣=Fm​≥m+1,
not from asymptotic dynamics. 
That is also its limitation. Once Proposition 2.11 has shown that the Parry weight depends only on the two endpoints, the proof is essentially a capacity count plus a rearrangement argument.  I would call it a genuine but small combinatorial-information-theoretic result, not a second major theorem in symbolic dynamics.
An honest extracted paper would therefore be built around:


Proposition 2.11;


Lemma 5.10;


Theorem 5.12;


Theorem 5.14;


perhaps a compressed version of Theorem 5.23 as the master endpoint-penalty identity.


That paper should be 8–10 pages, perhaps 12 at the absolute outside. It should not carry the rotation-discrepancy apparatus.
I would not identify any of the following as another independent paper:


Theorem 2.4: a neat uniqueness induction for Fibonacci weights, but too immediate by itself.


Theorem 3.4: a useful exact carry-boundary criterion, but another local arithmetic lemma, not a substantial second theorem.


Proposition 5.22: an exact constant-gap computation requiring a long golden-slope audit, but much less valuable than the amount of machinery used to obtain it.


Theorem 5.25: broader in wording, but its proof is just “Sturmian block support is O(m)” plus “primitive-SFT Parry cylinders are O(λ−m).” 


So my answer is yes, narrowly: Theorem 5.14 is the paper inside the paper. If you do not regard that finite placement problem as independently interesting, then there is no second paper to rescue. I would not manufacture one out of Sections 3 or 5.5.
(2) If the headline theorem is to be published at all
Theorem 4.1 should be presented as an elementary Fibonacci-normalization note, not as a dynamical rigidity theorem.
Its honest content is:


two equal-length circle intervals overlap exactly when their length exceeds the distance between their initial points;


this decides whether 00 and 11 occur;


in the sparse regime the realized language is already golden-mean;


in the dense regime complementation puts it in the golden-mean language, and the residue characterization proves injectivity;


in the middle regime 00 and 11 collide already at m=2.


That is precisely how the proof runs.  The “all resolutions” language is formally correct, but it should not be sold as evidence of depth: the theorem itself says that all-resolution injectivity is equivalent to injectivity at resolution two. 
A candid title would be something like:
Collision-Free Fibonacci Normalization of Binary Rotation Words
or
A Two-Letter Criterion for Fibonacci Folding of Rotation Languages
The paper should be 6–8 pages, with 10 pages as a hard ceiling. It needs only:


a concise definition of the Fibonacci/Zeckendorf fold;


Proposition 2.5 and Proposition 2.6, preferably combined into one lemma giving the residue description; 


Theorem 4.1;


Corollary 4.2;


one short example illustrating the three window regimes.


Theorem 4.4 should become a sentence or a remark: once the block map is a bijection on the realized alphabet, coordinatewise relabeling of the ordinary higher-block presentation is automatically a conjugacy. The proof in the manuscript is exactly that observation.  The circle-homeomorphism transfer in Theorem 4.5 should be deleted; it merely pulls the coding back through a conjugacy and reproduces the same symbolic sequence term by term. 
Venue and probability
The Fibonacci Quarterly, with an estimated 45% acceptance probability after a genuine 6–8 page rewrite.
That is the honest subject home: the journal explicitly centers Fibonacci numbers and related sequences, and this note is fundamentally about Fibonacci weights, Zeckendorf normalization, and a sharp elementary property of that normalization. Fibonacci Association
The probability is not higher because a referee may still conclude that the entire result is an attractive exercise once Proposition 2.6 is written down. The shortness and candor would help: a six-page note asks the journal to value one clean observation; a 48-page manuscript asks the referee to believe the observation supports a research program.
I would not lead with the Journal of Integer Sequences. Its stated focus is integer sequences and closely related topics, whereas the theorem is about a finite normalization map on symbolic block languages rather than a result about an integer sequence. 滑铁卢大学计算机科学系 Integers is a possible fallback, but its broader combinatorial-number-theory remit makes the slightness of the proof more conspicuous rather than less; it officially prefers original work connecting combinatorics and number theory. 科尔盖特大学数学系 My rough probability there would be about 30%.
Do not combine Theorem 4.1 and Theorem 5.14 merely to reach conventional article length. They are two different small notes, and joining them is what produced much of the present inflation.
(3) What the discrepancy and Parry-measure material is doing
Sections 2.3, 3.1 and 3.3: entirely support, not a second result
The discrepancy material answers a finite-sampling question that Theorem 4.1 does not require:

How close is the empirical histogram from N rotation iterates to the limiting block law?

Theorem 3.2 counts at most 2m interval atoms—or m+1 in the Sturmian case—and multiplies that count by star discrepancy.  That is a correct deterministic sampling bound, but it has no role in proving the collision classification. It could be stated for any deterministic map applied to a finite interval partition; the manuscript itself acknowledges that discrepancy uses only determinism of the fold. 
Section 3.3 then performs the standard conversion
TV control+lower bound on the smallest atom⟹KL control.
The general-window Theorem 3.12 is obtained by inserting the 2mDN∗​ estimate and the minimum partition-gap bound into the elementary finite-alphabet inequality.  The Sturmian variants in Proposition 3.13 and Corollaries 3.14 and 3.16 improve the constants but do not introduce a new phenomenon. 
None of this is needed for Theorem 4.1. It is there to justify the manuscript’s “sampling versus limiting law” narrative. That narrative is valid, but it is a separate elementary estimation exercise, not a reason for the headline theorem to occupy a dynamical-systems article.
Section 3.2: a separate lemma, but still not a second paper
Theorem 3.4 gives the exact criterion for failure of folding and prefix truncation to commute:
um+1​=1,Nm​(u1​⋯um​)≥Fm+1​.

This is genuinely specific to the canonical fold and is more than a discrepancy estimate. But it is another local Fibonacci carry threshold. It is not used to prove Theorem 4.1, nor does it develop into a projective-limit theorem, a classification of compatible folds, or a dynamical invariant. The manuscript defines a residual, proves a pointwise mismatch criterion, and then bounds the residual by its empirical frequency. That is useful internal bookkeeping, not an independent research contribution strong enough to support a paper.
In the headline note, delete the whole subsection.
Sections 5.1–5.2: scaffolding for the one viable second result
The Parry material begins with the key special fact: golden-mean Parry cylinder weights collapse to three endpoint classes.  From that, Theorem 5.5 obtains the exact KL identity involving entropy and the difference of the 11 and 00 endpoint masses.  Proposition 5.8 obtains the order-uniform ±logϕ Rényi window by observing that every cylinder weight differs from the central scale by at most a factor of ϕ. 
These are clean formulas, but by themselves they are identities generated by the endpoint collapse. Their purpose is to set up the support and placement optimization in Theorems 5.12 and 5.14.
The fiber-uniform lift decomposition in Proposition 5.1 is even more plainly auxiliary: it is the standard KL chain rule across the fibers of a deterministic map.  It does not contribute to the collision theorem and need not appear in either extracted note unless the authors specifically want a short interpretive remark.
Section 5.3: this is the second result
This is the part that can stand alone. Theorem 5.14 asks a well-defined finite optimization question and gives an exact answer, including optimizer classification across all Rényi orders. It does not make Theorem 4.1 deeper, but it is an independently readable theorem.
It should therefore be extracted rather than used to bulk up the window-classification note.
Section 5.4: consequences, not another theorem
Proposition 5.17 bounds every Rényi entropy of a bounded-type Sturmian m-block law by logm+Oα​(1).  Corollary 5.18 substitutes that estimate into Theorem 5.14 to obtain
mlogϕ−logm+Oα​(1).

This is useful context for the placement theorem, but the linear-minus-logarithmic scale is not an additional discovery once one knows that the source has m+1 atoms of roughly 1/m and the ambient Parry cylinders have mass roughly ϕ−m.
The golden-slope audit in Lemmas 5.19–5.21 occupies several pages to compute the exact endpoint imbalance and hence the constant gap in Proposition 5.22.   That calculation is correct and rather laborious, but the output is one additive constant:
(1−ϕ−3)logϕ.
 It should be an optional final proposition in the placement note, not five pages of central architecture.
Section 5.5: an attempted broadening that does not broaden the paper meaningfully
The primitive-SFT result says that individual Parry cylinders have exponentially small mass, while a finite-block factor of a Sturmian shift has only linearly many words. Consequently an injective placement has divergence at least
mlogλ−logm−O(1).
The proof explicitly uses only the Parry cylinder formula and
∣suppσm​∣≤m+ℓ+1.
 
This is not the missing broader dynamical theorem. It is a general support-budget inequality. The manuscript itself carefully concedes that the subsection offers no primitive-SFT optimizer classification or finite-block rigidity analogue. 
I would delete it from both extracted notes. At most it belongs in a closing paragraph as a one-line general observation.
Section 6: pure illustration
There is no ambiguity here. Section 6 expressly says that it “does not add new estimates” and only illustrates the preceding chain.  The tables confirm that finite-sample discrepancy can be small while the deterministic Parry gap remains large. They prove nothing needed by either principal theorem.
Delete the entire section from a research submission. One small example or table might survive in an expository version, but not in either short note.
Concrete disposition
There are two possible short notes, not one 48-page article:


Theorem 4.1 note: 6–8 pages, Fibonacci Quarterly, approximately 45%.


Theorem 5.14 note: 8–10 pages, built around the endpoint-weight optimization. I would regard this as the stronger and more independently interesting of the two, although still modest.


The discrepancy material is all supporting apparatus. The Parry material contains one second result—Theorem 5.14—but most of the rest is either scaffolding for it or increasingly elaborate refinement of a three-weight endpoint calculation. The present length comes from treating every intermediate identity, transfer, asymptotic corollary, endpoint audit, general-envelope observation, and numerical check as a separate contribution. They are not separate contributions.
