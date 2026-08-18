(1) What is the one result?
There is one result worth a specialist’s attention. It is not the compatible-restriction lemma, the general span-r statement, the covariance formulas, the pentagon, or the thermodynamic formalism.
The one-sentence result is:

Despite unbounded Fibonacci carry cascades, for every m≥3 the sliding code formed from length-m Zeckendorf folds is a topological conjugacy onto its image, and its causal inverse has exact memory 2: the current raw digit is determined by three consecutive fold labels, but not by two, independently of m.

The theorem to name is Theorem 5.3, “Exact causal decoder,” with Theorem 5.5 giving the resulting topological conjugacy. The exact statement is that ηt​ is recovered from (yt−2​,yt−1​,yt​), while (yt−1​,yt​) never suffices uniformly.  Theorem 5.5 turns that decoder into a sliding-block inverse for every m≥3. 
Theorem 5.2 is the substantive arithmetic backbone and sharp finite-block companion, not a competing headline: whole blocks become uniquely reconstructible at length 2m−1, with collisions still occurring at 2m−2.  The contrast between this m-scale whole-block threshold and the uniform three-label recovery of one digit is precisely what makes the result interesting; the manuscript itself distinguishes the two recovery problems. 
That is a genuine result. It is conceptually surprising because the underlying Fibonacci rewrite process has arbitrarily long cascades, yet the induced sequence code has a uniformly local causal inverse. 
The rest divides into two categories:


The four-state carry presentation and the strictly sofic discrepancy factor are useful structural analysis of the example.


Most subsequent statistics, covariance formulas, power spectrum, rotation polygon, and weighted-fiber thermodynamics are consequences of having identified that finite graph, not separate advances. The manuscript itself says that after the graph is known, the later formulas follow from standard Parry-measure and transfer-matrix calculations.  It likewise describes the rotation-set argument as the standard cycle method and Appendix D as linear algebra and symbolic elimination.  


So my honest assessment is:
One modest but real theorem, supported by a complete analysis of one explicit model. That is enough for a correctly sized specialist journal. It is not enough for a top symbolic-dynamics journal, because it does not produce a general method or a class-level theorem containing the Fibonacci example.
The paper should be titled and abstracted around exact decoding. A better title would be something like:

Finite-window Zeckendorf folding: exact decoding and the pair shift

The current title foregrounds compatible restriction, which is not what a reader will remember.

(2) The span-r theorem
A numbering point: in the attached version, the result is Theorem 4.4, not Theorem 3.1. Theorem 3.1 in this PDF is the elementary reversal/rewrite lemma.
Recommendation: remove it from the abstract
Choose the second option. Theorem 4.4 should leave the abstract entirely.
Making the proposed substitution is sensible housekeeping if the result remains in the body, but it does not turn the theorem into an abstract-level contribution.
There are four reasons.
First, the current advertised class is editorially indefensible
The definition requires a terminating confluent rewrite scan with support at most r, plus zero synchronization and the bounded-cascade clause.  The paper provides no nondegenerate member, and explicitly says its own Fibonacci map is not one.
Your finite search does not formally prove that no larger-rule system can ever furnish an instance. But that distinction does not rescue the manuscript. For publication purposes, the burden is on a paper advertising a “general structural theorem” to provide at least one natural example. An extensive search finding only 101 degenerate systems, none even remotely normalizing onto Xm​, makes the absence of an example conspicuous rather than incidental.
A referee will quite reasonably ask: generalizing what?
Second, the proposed substitution reveals that this is a bounded-delay lemma, not a normalization theorem
The proof uses the fact that all earlier coordinates are frozen outside the terminal r−1 window, and then uses zero synchronization to pass to the interior language. It does not use confluence or termination as mathematical inputs. 
Once the hypothesis is stated directly as bounded rightward influence or bounded causal delay, the conclusion becomes nearly the standard graph construction for a one-sided block map: continuation depends on a bounded terminal state, hence there are finitely many follower states.
That is correct and useful, but it is not a theorem that raises the paper’s significance.
Third, it still does not explain the Fibonacci result
Even after the substitution, Fibonacci normalization remains outside the class whose bounded delay supplies the graph. The four-state Fibonacci graph still comes from a separate arithmetic carry invariant. Thus the general theorem neither contains the main example nor proves the paper’s main decoder theorem.
It is an expository contrast:

bounded influence gives finite memory automatically; Fibonacci lacks bounded influence, so a carry invariant is needed.

That belongs in a remark or preliminary lemma, not in the abstract.
Fourth, keeping it in the abstract makes the paper look more general than it is
The present abstract gives the span-r theorem a full sentence immediately before the actual Fibonacci and decoding results.  A referee then discovers that:


no natural member is exhibited;


the central Fibonacci map is expressly excluded;


the proof uses only a bounded-delay condition; and


no subsequent Fibonacci result depends on it.


That sequence damages confidence in the significance framing even though the mathematics is correct.
What to do in the body
Retain at most a one-page lemma, renamed something like:

Bounded-delay pair criterion.

Define the hypothesis directly in terms of:


an idempotent projection onto the stable language;


pointwise fixation of stable words;


compatibility with high-order zero padding;


one-sided influence delay at most r−1.


Do not retain “rewrite span r” after removing the rewrite scan: r is then a delay or memory parameter, not rewrite support.
Give the window-3 projection explicitly as an example. That settles nonvacuity immediately. Then say that Fibonacci folding is not bounded-delay and requires the separate carry argument.
The exhaustive computer search need not appear in the paper. It has done its job by identifying a bad formulation.
A suitable abstract would instead begin:

For every m≥3, the sliding code obtained from length-m Zeckendorf folds is a topological conjugacy onto its image. Its causal inverse has exact memory 2, independently of m, while whole-block reconstruction has the sharp threshold 2m−1.

Then mention the four-state carry presentation and, at most, the strictly sofic discrepancy factor.

(3) Venue and odds
Strongest genuinely plausible venue: Dynamical Systems
My subjective submission-level probability, after the restructuring below, is approximately 35%, with a reasonable range of 30–40%.
For the present 35-page version, I would put it closer to 15–20%, because the actual theorem is buried among an uninstantiated general statement and a long series of standard finite-state consequences.
Dynamical Systems explicitly includes topological and ergodic dynamics, but it also says that papers should constitute a major advancement rather than a minor improvement. The exact, m-independent decoder theorem can make a plausible case as a sharp and complete result about a natural arithmetic recoding; the existing “many exact outputs from one four-state graph” presentation is much more vulnerable to being classified as minor. 泰尔与方在线
Why not the next one up: Discrete and Continuous Dynamical Systems
I would put DCDS-A at roughly 10–15%, which is not genuinely plausible enough to recommend.
Recent symbolic-dynamics papers there typically introduce a reusable notion or solve a problem over a substantial class—for example, broad soficity theorems for free extensions or a systematic theory of finite spacer rank—not merely determine every invariant of one explicit recoding. 美国数学科学研究院+1
This manuscript’s strongest statement is:


sharp;


elegant;


nontrivial;


confined to one Fibonacci folding map.


Its methods do not presently produce an analogous theorem for a natural class of numeration systems. Once Theorem 4.4 is correctly demoted, there is no class-level structural theorem to justify DCDS-A.
ETDS is farther out of range. Its own description emphasizes major contributions and central problems of the field; this paper is a polished case study, not a contribution at that scale. 剑桥大学出版社 I would assign ETDS below 5% on significance.
Cut; do not split
Splitting would produce two papers weaker than the present one:


a decoder/conjugacy paper with too little structural context;


a transfer-matrix/statistics paper that is mainly calculation once the graph is known.


The second is not a viable standalone specialist paper.
I would make the following cuts:


Keep and foreground Theorems 5.2, 5.3, and 5.5. These are the paper.


Keep the four-state carry presentation and Theorem 4.7. The strictly sofic discrepancy factor is a worthwhile structural payoff.


Demote Theorem 4.4 to a brief bounded-delay lemma, outside the abstract.


Delete Section 6 and Appendix D. The weighted partition function, recurrence, CLT, large deviations, and entropy duality do not increase the venue ceiling enough to justify their length.


Compress Theorems 4.8–4.10 severely. Retain the density 4/9 and perhaps the CLT as concise corollaries; move the full covariance and rational power spectrum to supplementary material or omit them.


Keep the pentagon only if it can be presented in two pages. Treat it as a concrete corollary of cycle enumeration, not a second main theorem.


The target should be approximately 23–26 pages, not 35.
Final assessment
There is a publishable paper here, but its current significance narrative is backwards.
The memorable mathematics is:

an arithmetic sliding code built from increasingly large Zeckendorf windows has a uniformly local and sharp causal inverse.

The span-r theorem should not appear in the abstract. The transfer-matrix tail should be cut. Submit the concentrated decoder-and-carry paper to Dynamical Systems, with roughly a one-in-three chance of acceptance. In its current form, the most likely significance report is: “correct and impressively explicit, but overlong and without a sufficiently central theorem.”
