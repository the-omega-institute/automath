1. The single most valuable new result
My overall conclusion is negative in the strict sense requested: I do not see a named open problem that is both realistically reachable from the present machinery in one revision and strong enough to force a clear full-tier jump. The present mechanism extracts one specially synchronized orbit from an arbitrary infinite MCFL; it does not control the whole language, every sufficiently long word, or simultaneous representations in two numeration systems. That quantifier limitation is the structural ceiling.
There is, however, one realistically attainable theorem that is substantially better than another corollary and is the strongest plausible tier-raising addition.
Candidate 1 — Weak-Perron radical classification

Theorem (weak-Perron radical classification for bounded-support MCFLs).
Let U=(Un​)n≥0​ be a standard greedy linear numeration basis with U0​=1, strictly increasing integer place values with bounded quotients, and let RU​ be the LSD-first reversal of its greedy representation language. Suppose that the minimal tail recurrence polynomial μU​ is the minimal polynomial of a weak Perron number β>1, meaning that every conjugate β′ satisfies
∣β′∣≤β.
Let Sr​ be the set of prime divisors of μU​(0). Then the following are equivalent:


There exist k<∞ and an infinite k-MCFL L⊆RU​ such that
w∈Lsup​ωSrc​​(valU​(w))<∞.


RU​ contains a geometric synchronized scheme whose values are cbt, with c≥1, b≥2.


Some positive power of β is an integer:
βm=B∈Z≥2​for some m≥1.


For some m≥1 and B≥2,
μU​(X)∣Xm−B.


For some m≥1, B≥2, and n0​,
Un+m​=BUn​(n≥n0​).


In the positive case, RU​ already contains the infinite regular ray
{0n0​+mt1:t≥0},valU​(0n0​+mt1)=Un0​​Bt.
Consequently, if no positive power of β is an integer, then every infinite MCFL L⊆RU​ has
w∈Lsup​ωSrc​​(valU​(w))=∞.

Weak Perron numbers are a standard spectral class introduced in connection with nonnegative integral matrices; equivalently, some power is Perron, and they include non-Perron examples such as 2​. SciSpace
This theorem would strictly extend the manuscript’s present Corollary 2.25, which assumes strict Perron dominance and concludes positivity exactly for integral β.  It would reveal that the correct boundary beyond the primitive Perron case is not “β is an integer” but rather “β has an integral power.”
That distinction produces genuinely new positive systems. For example,
U2t​=6t,U2t+1​=2⋅6t
has minimal polynomial X2−6, dominant root 6​, and a regular geometric ray 02t1 with values 6t. Thus the proposed theorem would identify an entire imprimitive, nonintegral exceptional class that the current strict-Perron statement deliberately excludes.
This is not merely another immunity consequence. It changes the classification theorem itself, replaces a sufficient spectral hypothesis by the natural weak Perron boundary, and proves an exact equivalence among language structure, arithmetic support, algebraic conjugacy, and eventual scalar periodicity.
Candidate 2 — Elimination of strict length ordering

Theorem (length-order-free recurrent representation theorem).
Assume conditions (U1), (U2), and (U4), but omit (U3). Thus valU​:RU​→N≥1​ remains a bijection, but shorter canonical words need not have smaller values. Then every infinite k-MCFL L⊆RU​ contains a synchronized family
W(t)=au1​v1t​w1​s1t​⋯uk​vkt​wk​skt​uk+1​
whose values N(t) are pairwise distinct and satisfy
N(t+H(q))≡N(t)(modq)
for every q coprime to a0​. Moreover, all of the following remain valid without (U3):


the no-isolated-point and scattered-set obstruction;


the nonunit support/valuation dichotomy and prime MCF-immunity;


the minimal-tail geometric-ray characterization;


in the unit case, arbitrarily deep increasing quotient chains and the induced divisibility tree.



This is very likely correct. The present proof uses (U3) at the end of Theorem 2.7 only to turn increasing word length into increasing numerical value.   But positive pumped length makes the words W(t) distinct, and the bijectivity in (U2) already makes their values distinct. For a required increasing step, one can take a sufficiently large multiple of the return time: infinitely many distinct positive integers in one congruence class cannot all lie below the current value.
This would improve the axiomatic theorem significantly, but I would not count it as a full-tier raiser by itself. It removes a convenient hypothesis; it does not introduce a new standard-object classification or new mechanism.
Candidate 3 — General decidability of the geometric-ray property

Theorem (decidability of bounded outside-prime support).
On the promised class of finite presentations consisting of a digit alphabet, recurrence and initial data, a DFA for RU​, and a certified minimal tail recurrence with threshold, there is an algorithm deciding whether
∃k<∞∃infinite k-MCFL L⊆RU​:w∈Lsup​ωSrc​​(valU​(w))<∞.
Equivalently, the algorithm decides whether RU​ contains a geometric synchronized scheme.

This would unquestionably raise the tier: it would turn the structural equivalence into a complete effective classification. The manuscript presently proves only positive semidecidability and explicitly identifies the absent computable witness bound.  
It is not, however, realistically attainable from the current machinery in one focused revision.
The hierarchy is therefore:


Weak-Perron radical classification: best realistic tier-raising candidate.


Removal of (U3): highly attainable, worthwhile, but not independently tier-raising.


General decidability: genuinely tier-raising, but presently out of reach.


The current paper’s repaired theorem package is substantial—the abstract accurately centers the all-modulus synchronized orbit, geometric-ray inverse theorem, positive semidecision boundary, and strict-Perron classification.  The repairs restore the baseline mathematical case; they do not themselves constitute an upward-tier result.

2. Reachability from the machinery already in the paper
Candidate 1: Weak-Perron radical classification — reachable as a difficult extension
The existing manuscript supplies almost the whole proof.
Existing inputs that feed the proof
First, Theorem 2.16 already gives
bounded outside support⟺geometric synchronized scheme.
Its proof extracts a fixed-support recurrence from the synchronized orbit, applies Evertse to eliminate multiple nondegenerate roots, applies Schur to eliminate the polynomial factor, and recodes the resulting arithmetic subsequence as cbt.  None of that requires strict Perron dominance.
Second, the present Corollary 2.25 already proves that a geometric synchronized scheme of total pumped length D satisfies
UL+Dt−1​≤cbt<UL+Dt​
and hence, under the current root asymptotic,
b=βD.
It then uses strict inequality ∣β′∣<β to conclude that β has degree one.  This is exactly the step to replace.
Third, the converse construction is already present in the integral case: when the tail satisfies Un+1​=BUn​, the words 0Jr​+t1 form a geometric ray.  The weak-Perron converse merely changes the step size from 1 to m.
The genuinely new ingredient
One new asymptotic lemma is needed.

Lemma. Let U be an eventually positive, strictly increasing integer recurrence whose minimal tail polynomial is the minimal polynomial of a weak Perron number β>1. Then
n→∞lim​Un1/n​=β.
More precisely, for some h≥1 such that βh is Perron, each residue subsequence satisfies
Uhn+r​=Cr​(βh)n+o((βh)n)
with Cr​>0.

The weak Perron property gives an h for which the equal-modulus conjugates coalesce after taking h-th powers. SciSpace Minimality ensures that at least one residue class has a nonzero dominant coefficient. Strict increase then forces every residue class to have a nonzero positive dominant coefficient: a residue class of smaller exponential growth immediately following one of growth βhn would eventually violate Un​<Un+1​.
Once this lemma is proved, the current greedy interval argument gives
b=βD.
Since b∈Z≥2​, the minimal polynomial of β divides XD−b. Conversely, if
μU​(X)∣Xm−B,
then Xm−B annihilates the tail, so
Un+m​=BUn​
eventually, and 0n0​+mt1 gives the required regular ray.
No new MCFL lemma, no new S-unit theorem, and no new adic topology are needed. The missing work is a careful weak-Perron recurrence-asymptotics lemma and exact handling of thresholds. This is a difficult but natural extension of the current proof, not a separate research programme.
Candidate 2: Removal of (U3) — very reachable
The proof modifications are local.
For Theorem 2.7, positive pumped length gives
∣W(t+1)∣>∣W(t)∣,
so the words W(t) are distinct. Since valU​ is injective on RU​, the values N(t) are pairwise distinct. That is enough for the no-isolated-point argument: N(t+H(q)) is congruent to N(t) and is a different point.
The arithmetic rigidity lemma should be restated with “pairwise distinct positive integer recurrence” in place of “strictly increasing positive integer recurrence.” After Evertse and Schur reduce a residue subsequence to
cλn,
positivity implies λ>0, integrality implies λ∈Z, and pairwise distinctness excludes λ=1. Hence λ≥2. The current rationality and Schur argument already supplies everything else. 
For the unit quotient-chain theorem, suppose N(ti​) has been selected and let H be a return time modulo Mi​N(ti​)ri​+1. Every
N(ti​+mH)
lies in the same congruence class. These values are pairwise distinct; only finitely many positive integers are below N(ti​), so some sufficiently large m gives
N(ti​+mH)>N(ti​).
The rest of the divisibility argument is unchanged. The current proof already allows taking a sufficiently large positive multiple of a return time in the tree construction. 
The genuinely new ingredient is therefore only a strengthened formulation of Lemma 2.15 and consistent replacement of “strictly increasing orbit” by “injective orbit, with increasing selections when required.”
This should probably be done even if the weak-Perron theorem is not pursued. It makes clear that the arithmetic mechanism rests on uniqueness, not on genealogical length order.
Candidate 3: General decidability — not reachable from the present machinery
The paper already has:


effective enumeration of all proposed schemes;


a decision procedure for whether a fixed proposed scheme lies in RU​ for every t;


a recurrence-order bound (dr​+1)2k for testing the exact identity N(t+1)=bN(t);


equivalence between existence of such a scheme and bounded outside-prime support. 


What it lacks is not another recurrence calculation. It lacks a compactness or compression theorem of the form
positive instance⟹positive witness of computably bounded fan-out and block length.
The DFA transition monoid cannot supply that bound because replacing a word by a shorter word with the same automaton endpoints does not preserve its affine matrix. The manuscript states this obstruction accurately. 
A solution would require genuinely new theory, such as one of the following:


an effective bounded-witness theorem for rational subsets of the special affine matrix semigroups generated by the digit actions;


a structural classification of all products
C0​B1t​C1​⋯Bmt​Cm​
whose selected scalar coordinate is exactly geometric;


or an undecidability reduction that preserves injective canonical representation, strict positivity, eventual companion recurrence, and the DFA interface.


None of those follows from the existing pumping orbit, Cayley–Hamilton, Evertse, or finite transition monoid. This is a different research project.
The 2026 substitution lemma does not close this gap. It is an all-sufficiently-long-word necessary condition for MCFLs, introduced precisely as an alternative to unavailable strong pumping; its output is not a fixed simultaneous-power orbit. arXiv The manuscript’s explanation of why the switchable-tuple alternative does not yield fixed affine matrix powers is mathematically on point. 

3. Ranking by success probability multiplied by tier impact
Here “success probability” means the chance of a complete, referee-resistant proof in one focused revision from the current manuscript. The product is the raw percentage multiplied by the 1–10 impact score.
RankCandidateSuccess probabilityTier impactProduct1Weak-Perron radical classification68%7.5/105102Eliminate strict length ordering (U3)90%4.5/104053General decidability of geometric-scheme existence12%9.5/10114
Calibration
Weak-Perron classification: 68% × 7.5 = 510.
The proof path is clear and uses the current inverse theorem and greedy interval argument almost verbatim. The main risk is not conceptual but technical: proving the weak-Perron residue asymptotics with all coefficients and tail thresholds handled correctly, and ensuring that the proposed class of greedy systems is standard and nonempty beyond toy examples. Its impact is high because it replaces the current strict-dominance endpoint by an exact algebraic classification with new nonintegral positive cases. It is still an extension of the same mechanism, so I would not score it 9 or 10.
Removal of (U3): 90% × 4.5 = 405.
The necessary substitutions are visible in the existing proofs. The main danger is overlooking one later use of monotonicity, but the quotient-chain selection argument appears to repair all such uses. This makes the abstract theorem cleaner and broader but does not connect it to a named external problem or materially alter the mechanism.
General decidability: 12% × 9.5 = 114.
A correct result would transform the paper, but the missing step is exactly the hard global issue, not an omitted lemma. The present proof offers candidate verification but no means of bounding the candidate search. One revision is unlikely to produce either a compression theorem or a preserving undecidability reduction.
There is therefore no candidate with both success probability above 50% and tier impact at least 8/10. That is why I do not regard a clear full-tier jump as presently reachable. Candidate 1 is the best available move and may raise the paper within or across a nearby boundary, but it does not eliminate the structural ceiling.

4. Which standard tier-raising levers apply
(a) Settling a named open problem in the literature — does not presently apply
The nearest genuinely named problem is the degeneracy/Cobham-extension problem for context-free or pushdown-automatic sequences: characterize when such a sequence is actually automatic, possibly in another base, and seek an analogue of Cobham’s base-dependence theorem. Le Gonidec explicitly lists this as an open problem. SciSpace
The current manuscript cannot realistically settle it. A Cobham-type theorem compares the global structure of one set or sequence in two multiplicatively independent representations. The manuscript’s weak pumping input gives only one synchronized ray inside one infinite MCFL. Two languages representing the same set could supply two unrelated rays with no common values. Nothing in the current machinery controls their intersection or the rest of either language.
This is the decisive quantifier mismatch:
∃ one pumpable orbit⇒global control of a language or sequence in two bases.
Attempting the Cobham problem would require new substitution/dynamical or global language theory, not a refinement of the affine return argument.
(b) Proving something about the field’s standard objects — applies through Candidate 1
The present Corollary 2.25 already moves from the paper’s abstract systems to standard greedy linear numeration bases with Perron recurrence. 
The proposed extension would treat standard greedy bases with weak Perron recurrence—the imprimitive Perron–Frobenius case—rather than only strictly dominant Perron roots. Weak Perron numbers are standard algebraic/spectral objects and are strictly broader than Perron numbers. SciSpace
The exact standard-object conclusion would be:
bounded-support infinite MCFL exists⟺βm∈Z for some m≥1​
rather than the present
bounded-support infinite MCFL exists⟺β∈Z​
under strict Perron dominance.
That is the strongest applicable lever.
(c) Removing a hypothesis assumed for convenience — applies twice
The more important removable hypothesis is:
∣β′∣<βfor all other conjugates
in Corollary 2.25. It should be replaced by the weak condition
∣β′∣≤β,
with the conclusion correspondingly sharpened from “β is integral” to “some power of β is integral.”
This is not merely weakening an assumption while retaining the same conclusion; the 6​ example shows that the conclusion must change. The proposed theorem would give the exact replacement.
The second removable hypothesis is (U3), strict length ordering. The synchronized orbit needs distinctness, which follows from positive pumped length plus injectivity of canonical representations. The paper currently builds (U3) into its ambient definition.  Removing it would clarify the true minimal interface.
Of these two, only the weak-Perron removal has substantial tier impact.
(d) A sharpness or matching-bound theorem — does not materially apply
The visible estimate is
H(q)≤∣GLd+1​(Z/qZ)∣≤q(d+1)2.

One could replace this by the exponent of the relevant finite subgroup or construct examples with long return times. That would sharpen the quantitative congruence statement, but the paper’s conclusions are qualitative: existence of a return time, absence of isolated points, fixed-support extraction, and quotient chains. None depends on the exponent being close to optimal.
A matching lower bound for H(q) would therefore improve a subsidiary estimate, not the paper’s mathematical status. The valuable sharpness result is algebraic rather than numerical: the weak-Perron theorem would show exactly why strict dominance yields only integer bases and precisely which imprimitive nonintegral exceptions survive.

5. Strongest remaining higher-tier objection after Candidate 1
Assume the weak-Perron radical classification has been proved in full strength, together with explicit nonintegral examples and the removal of (U3).
The strongest higher-tier objection would be:

The enlarged paper still has only one genuinely new mechanism: extract one weak-pumping orbit, obtain finite-group congruence returns, and pass that orbit through classical Evertse–Schur and Broughan inputs. The weak-Perron theorem completes the spectral boundary of one application, but it does not strengthen the underlying MCFL structure, solve a literature open problem, or make the geometric-ray property effectively decidable. Thus the new theorem is a sharp closure of the existing argument rather than a second conceptual advance.

That objection would be fair. The paper itself is explicit that its effectiveness stops at positive semidecidability because no computable witness-compression bound is known. 
Exact result that would resolve the objection
Prove the following bounded-witness theorem.

Uniform geometric-scheme compression theorem.
There is a computable function
B=B(∣Q∣, ∣A∣, dr​, Jr​,imax​∣ci​∣,0≤j<Jr​+dr​max​Uj​)
such that, for every promised regular canonical recurrent system presented by a DFA with state set Q, if the system admits any geometric synchronized scheme, then it admits one whose fan-out k and total length of all constant and pumped blocks are at most B.

Together with the manuscript’s existing candidate-verification procedure, this would immediately give a terminating decision algorithm for both positive and negative instances. It would make the synchronized-ray mechanism itself—not merely one successful arithmetic application—the central theorem.
I do not regard that compression theorem as reachable from the present machinery in one revision. Without it, the honest ceiling is:


the weak-Perron classification is the strongest realistic mathematical addition;


removal of (U3) is an important cleanup;


no named open problem is presently within reach;


and no clearly full-tier-raising theorem is available without importing a genuinely new global language-theoretic or matrix-semigroup idea.


Finally, the earlier proof-level objections appear substantially repaired in the attached main article. In particular, the rationality step now contains an explicit Hankel-rank and Galois argument before applying Schur and integrality.  The Zeckendorf proof is in the main text, the 2026 substitution lemma is discussed directly, and the effectivity theorem is now limited to promised inputs. Those changes restore mathematical credibility but do not raise the tier. The attached PDF says that the supplement and complete verification resources accompany the submission; because only main.pdf was available here, I have not independently verified those external files or the reported current hashes and outputs.